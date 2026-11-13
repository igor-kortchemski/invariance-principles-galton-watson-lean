/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.MonotoneDensity
public import BGW.StableTrees.Attraction.Defs

/-!
# Inversion of a regularly varying integer tail

Let `ν` be a probability measure on `ℤ` and `T(x) = ν.real {z | x < z}`.  If `T` is regularly
varying of index `-θ`, `θ > 0`, then the tail quantile `q_n = tailQuantile ν n` satisfies
`q_n → ∞`, `n T(q_n) → 1`; the multiplier quantile `q^c_n = inf {x ≥ 0 | T x ≤ c / n}`
satisfies `n T(q^c_n) → c` and `q^c_n / q_n → c ^ (-1/θ)`; and `q_{⌊λ n⌋} / q_n → λ ^ (1/θ)`.
Ported from `BGWLeaves/StableAnalysis/QuantileInversion.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.QuantileInversion

open BGW.StableTrees.Attraction BGW.StableTrees.Attraction.MonotoneDensity

/-- The properties of the tail function `T` used for the inversion. -/
structure TailData (T : ℝ → ℝ) (θ : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ T x
  anti : Antitone T
  rc : ∀ x, ContinuousWithinAt T (Ici x) x
  tendsto_nat : Tendsto (fun n : ℕ => T n) atTop (𝓝 0)
  theta_pos : 0 < θ
  rv : IsRegVaryAtTop T (-θ)

/-- Left-continuous inverse of `T` at level `a`. -/
noncomputable def levelQuantile (T : ℝ → ℝ) (a : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ T x ≤ a}

section Abstract

variable {T : ℝ → ℝ} {θ : ℝ}

theorem TailData.pos (h : TailData T θ) (x : ℝ) : 0 < T x := by
  have h1 : ∀ᶠ y : ℝ in atTop, T y ≠ 0 := by
    have := (h.rv 1 one_pos).eventually (isOpen_ne.mem_nhds (show ((1 : ℝ) ^ (-θ)) ≠ 0 by simp))
    filter_upwards [this] with y hy h0
    apply hy
    simp [h0]
  obtain ⟨X, hX⟩ := eventually_atTop.1 h1
  have hX' : 0 < T (max x X) :=
    lt_of_le_of_ne (h.nonneg _) (hX _ (le_max_right _ _)).symm
  exact lt_of_lt_of_le hX' (h.anti (le_max_left _ _))

theorem TailData.set_nonempty (h : TailData T θ) {a : ℝ} (ha : 0 < a) :
    {x : ℝ | 0 ≤ x ∧ T x ≤ a}.Nonempty := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.tendsto_nat.eventually (ge_mem_nhds ha))
  exact ⟨N, Nat.cast_nonneg _, hN N le_rfl⟩

theorem TailData.level_nonneg (h : TailData T θ) {a : ℝ} (ha : 0 < a) :
    0 ≤ levelQuantile T a :=
  le_csInf (h.set_nonempty ha) (fun _ hx => hx.1)

theorem TailData.tail_level_le (h : TailData T θ) {a : ℝ} (ha : 0 < a) :
    T (levelQuantile T a) ≤ a := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ x in 𝓝[≥] (levelQuantile T a), a < T x :=
    (h.rc _).eventually (lt_mem_nhds hlt)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  obtain ⟨s, hs, hsu⟩ := exists_lt_of_csInf_lt (h.set_nonempty ha)
    (show levelQuantile T a < u from hu)
  have hle : levelQuantile T a ≤ s :=
    csInf_le (⟨0, fun _ hx => hx.1⟩ : BddBelow {x : ℝ | 0 ≤ x ∧ T x ≤ a}) hs
  have := hsub ⟨hle, hsu⟩
  exact absurd hs.2 (not_le.2 this)

theorem lt_tail_of_lt_level {T : ℝ → ℝ} {a x : ℝ}
    (hx : 0 ≤ x) (hxQ : x < levelQuantile T a) : a < T x := by
  by_contra hle
  push Not at hle
  exact absurd
    (csInf_le (⟨0, fun _ hx => hx.1⟩ : BddBelow {x : ℝ | 0 ≤ x ∧ T x ≤ a}) ⟨hx, hle⟩)
    (not_le.2 hxQ)

theorem TailData.level_tendsto_atTop (h : TailData T θ) :
    Tendsto (levelQuantile T) (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro M
  filter_upwards [Ioo_mem_nhdsGT (h.pos M)] with a ha
  by_contra hM
  push Not at hM
  have h1 : T M ≤ T (levelQuantile T a) := h.anti hM.le
  have h2 := h.tail_level_le ha.1
  linarith [ha.2]

theorem rpow_neg_lt_of_lt {x y θ : ℝ} (hx : 0 < x) (hxy : x < y) (hθ : 0 < θ) :
    y ^ (-θ) < x ^ (-θ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.trans hxy).le]
  exact (inv_lt_inv₀ (Real.rpow_pos_of_pos (hx.trans hxy) _) (Real.rpow_pos_of_pos hx _)).2
    (Real.rpow_lt_rpow hx.le hxy hθ)

theorem TailData.level_ratio_tendsto (h : TailData T θ) :
    Tendsto (fun a => T (levelQuantile T a) / a) (𝓝[>] 0) (𝓝 1) := by
  have hθ := h.theta_pos
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨b', hb1, hb2⟩ := exists_between (max_lt hb zero_lt_one)
    have hb'0 : 0 < b' := lt_of_le_of_lt (le_max_right _ _) hb1
    have hbb' : b < b' := lt_of_le_of_lt (le_max_left _ _) hb1
    set μ : ℝ := b' ^ (1 / θ) with hμdef
    have hμ0 : 0 < μ := Real.rpow_pos_of_pos hb'0 _
    have hμ1 : μ < 1 := Real.rpow_lt_one hb'0.le hb2 (by positivity)
    have hμθ : μ ^ θ = b' := by
      rw [hμdef, ← Real.rpow_mul hb'0.le, one_div, inv_mul_cancel₀ hθ.ne', Real.rpow_one]
    have hlim : Tendsto (fun x => T (μ⁻¹ * x) / T x) atTop (𝓝 b') := by
      have := h.rv μ⁻¹ (inv_pos.2 hμ0)
      rwa [Real.inv_rpow hμ0.le, Real.rpow_neg hμ0.le, inv_inv, hμθ] at this
    have hx : Tendsto (fun a => μ * levelQuantile T a) (𝓝[>] 0) atTop :=
      h.level_tendsto_atTop.const_mul_atTop hμ0
    have hR := (hlim.comp hx).eventually (lt_mem_nhds hbb')
    filter_upwards [hR, self_mem_nhdsWithin, h.level_tendsto_atTop.eventually_gt_atTop 0]
      with a haR ha haQ
    have ha0 : (0 : ℝ) < a := ha
    have hxlt : μ * levelQuantile T a < levelQuantile T a := by nlinarith
    have hlow : a < T (μ * levelQuantile T a) :=
      lt_tail_of_lt_level (by positivity) hxlt
    have hcomp : (fun x => T (μ⁻¹ * x) / T x) ∘ (fun a => μ * levelQuantile T a) =
        fun a => T (levelQuantile T a) / T (μ * levelQuantile T a) := by
      funext a
      simp only [Function.comp, ← mul_assoc, inv_mul_cancel₀ hμ0.ne', one_mul]
    have haR' : b < T (levelQuantile T a) / T (μ * levelQuantile T a) := by
      have := haR
      simp only [Function.comp] at this
      rwa [← mul_assoc, inv_mul_cancel₀ hμ0.ne', one_mul] at this
    have hTx := h.pos (μ * levelQuantile T a)
    have hRnn : 0 ≤ T (levelQuantile T a) / T (μ * levelQuantile T a) :=
      div_nonneg (h.nonneg _) hTx.le
    set R := T (levelQuantile T a) / T (μ * levelQuantile T a) with hRdef
    have hTQ : T (levelQuantile T a) = R * T (μ * levelQuantile T a) := by
      rw [hRdef, div_mul_cancel₀ _ hTx.ne']
    rw [lt_div_iff₀ ha0]
    nlinarith
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : (0 : ℝ) < a := ha
    have := h.tail_level_le ha0
    calc T (levelQuantile T a) / a ≤ 1 := (div_le_one ha0).2 this
      _ < b := hb

/-- If `T(r n) / T(s n) → c > 0` and `s n → ∞`, then `r n / s n → c ^ (-1/θ)`. -/
theorem TailData.ratio_tendsto (h : TailData T θ) {r s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {c : ℝ} (hc : 0 < c) (hrs : Tendsto (fun n => T (r n) / T (s n)) atTop (𝓝 c)) :
    Tendsto (fun n => r n / s n) atTop (𝓝 (c ^ (-1 / θ))) := by
  have hθ := h.theta_pos
  set L : ℝ := c ^ (-1 / θ) with hLdef
  have hL0 : 0 < L := Real.rpow_pos_of_pos hc _
  have hLθ : L ^ (-θ) = c := by
    rw [hLdef, ← Real.rpow_mul hc.le]
    have : -1 / θ * -θ = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hspos : ∀ᶠ n in atTop, 0 < s n := hs.eventually_gt_atTop 0
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨b', hb1, hb2⟩ := exists_between (max_lt hb hL0)
    have hb'0 : 0 < b' := lt_of_le_of_lt (le_max_right _ _) hb1
    have hbb' : b < b' := lt_of_le_of_lt (le_max_left _ _) hb1
    have hcmp : c < b' ^ (-θ) := by
      rw [← hLθ]; exact rpow_neg_lt_of_lt hb'0 hb2 hθ
    have hlim := (h.rv b' hb'0).comp hs
    filter_upwards [hspos, hrs.eventually_lt hlim hcmp] with n hn hlt
    simp only [Function.comp] at hlt
    have hT := h.pos (s n)
    have hlt' : T (r n) < T (b' * s n) := (div_lt_div_iff_of_pos_right hT).1 hlt
    refine lt_of_lt_of_le hbb' ?_
    by_contra hcon
    push Not at hcon
    have h1 : r n ≤ b' * s n := by rw [div_lt_iff₀ hn] at hcon; exact hcon.le
    exact absurd (h.anti h1) (not_le.2 hlt')
  · intro b hb
    have hb0 : 0 < b := hL0.trans hb
    have hcmp : b ^ (-θ) < c := by
      rw [← hLθ]; exact rpow_neg_lt_of_lt hL0 hb hθ
    have hlim := (h.rv b hb0).comp hs
    filter_upwards [hspos, hlim.eventually_lt hrs hcmp] with n hn hlt
    simp only [Function.comp] at hlt
    have hT := h.pos (s n)
    have hlt' : T (b * s n) < T (r n) := (div_lt_div_iff_of_pos_right hT).1 hlt
    by_contra hcon
    push Not at hcon
    have h1 : b * s n ≤ r n := by rwa [le_div_iff₀ hn] at hcon
    exact absurd (h.anti h1) (not_le.2 hlt')


theorem TailData.level_seq (h : TailData T θ) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 < a n) :
    Tendsto (fun n => levelQuantile T (a n)) atTop atTop ∧
      Tendsto (fun n => T (levelQuantile T (a n)) / a n) atTop (𝓝 1) := by
  have hn : Tendsto a atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨ha, hpos⟩
  exact ⟨h.level_tendsto_atTop.comp hn, h.level_ratio_tendsto.comp hn⟩

theorem TailData.level_mul_tail (h : TailData T θ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * T (levelQuantile T (c / n))) atTop (𝓝 c) := by
  have ha : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < c / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  have := (h.level_seq ha hpos).2.const_mul c
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem TailData.level_ratio_one (h : TailData T θ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => T (levelQuantile T (c / n)) / T (levelQuantile T (1 / n))) atTop
      (𝓝 c) := by
  have h1 := h.level_mul_tail hc
  have h2 := h.level_mul_tail one_pos
  have := h1.div h2 one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  have hp := (h.pos (levelQuantile T (1 / n))).ne'
  simp only [Pi.div_apply]
  field_simp

end Abstract

section Measure

variable (ν : Measure ℤ) [IsProbabilityMeasure ν]

private theorem rightTail_tendsto_zero :
    Tendsto (fun n : ℕ => ν {z : ℤ | (n : ℤ) < z}) atTop (𝓝 0) := by
  let s : ℕ → Set ℤ := fun n => {z | (n : ℤ) < z}
  have hanti : Antitone s := by
    intro m n hmn z hz
    change (n : ℤ) < z at hz
    change (m : ℤ) < z
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hz
  have hinter : (⋂ n, s n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz' := (Set.mem_iInter.mp hz) (z.natAbs + 1)
    change ((z.natAbs + 1 : ℕ) : ℤ) < z at hz'
    omega
  have hfinite : ν (s 0) ≠ ∞ := measure_ne_top _ _
  have h := tendsto_measure_iInter_atTop (μ := ν) (s := s)
    (fun n => (MeasurableSet.of_discrete : MeasurableSet (s n)).nullMeasurableSet)
    hanti ⟨0, hfinite⟩
  simpa [Function.comp_def, s, hinter] using h

theorem tailData_of_regVary {θ : ℝ} (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    TailData (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) θ where
  nonneg x := measureReal_nonneg
  anti := by
    intro x y hxy
    exact measureReal_mono (fun z hz => lt_of_le_of_lt hxy hz)
  rc := by
    intro x
    refine (continuousWithinAt_const (b := ν.real {z : ℤ | x < (z : ℝ)})).congr_of_eventuallyEq
      ?_ rfl
    filter_upwards [Ico_mem_nhdsGE (show x < (⌊x⌋ : ℝ) + 1 from Int.lt_floor_add_one x)] with y hy
    have hfl : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨(Int.floor_le x).trans hy.1, hy.2⟩
    have hset : {z : ℤ | y < (z : ℝ)} = {z : ℤ | x < (z : ℝ)} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      rw [← Int.floor_lt, ← Int.floor_lt, hfl]
    simp only [hset]
  tendsto_nat := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (rightTail_tendsto_zero ν)
    refine h.congr (fun n => ?_)
    simp only [Function.comp, measureReal_def]
    congr 2
    ext z
    simp only [Set.mem_ofPred_eq]
    exact_mod_cast Iff.rfl
  theta_pos := hθ
  rv := hT

/-- Multiplier quantile `inf {x ≥ 0 | P[W > x] ≤ c / n}`. -/
noncomputable def multQuantile (c : ℝ) (n : ℕ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ ν.real {z : ℤ | x < (z : ℝ)} ≤ c / n}

omit [IsProbabilityMeasure ν] in
theorem tailQuantile_eq (n : ℕ) :
    tailQuantile ν n = levelQuantile (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (1 / n) := rfl

omit [IsProbabilityMeasure ν] in
theorem multQuantile_eq (c : ℝ) (n : ℕ) :
    multQuantile ν c n = levelQuantile (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (c / n) := rfl

variable {ν}
variable {θ : ℝ}

/-- (a) The tail quantile tends to infinity. -/
theorem tailQuantile_tendsto_atTop (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun n : ℕ => tailQuantile ν n) atTop atTop := by
  have h := tailData_of_regVary ν hθ hT
  have ha : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < 1 / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  exact (h.level_seq ha hpos).1

/-- (b) `n * T(q_n) → 1`. -/
theorem tailQuantile_mul_tail (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real {z : ℤ | tailQuantile ν n < (z : ℝ)}) atTop
      (𝓝 1) :=
  (tailData_of_regVary ν hθ hT).level_mul_tail one_pos

/-- (c) The multiplier quantile tends to infinity. -/
theorem multQuantile_tendsto_atTop (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) {c : ℝ}
    (hc : 0 < c) : Tendsto (fun n : ℕ => multQuantile ν c n) atTop atTop := by
  have h := tailData_of_regVary ν hθ hT
  have ha : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < c / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  exact (h.level_seq ha hpos).1

/-- (c) `n * T(q^c_n) → c`. -/
theorem multQuantile_mul_tail (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real {z : ℤ | multQuantile ν c n < (z : ℝ)}) atTop
      (𝓝 c) :=
  (tailData_of_regVary ν hθ hT).level_mul_tail hc

/-- (c) `q^c_n / q_n → c ^ (-1/θ)`. -/
theorem multQuantile_div_tailQuantile (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => multQuantile ν c n / tailQuantile ν n) atTop
      (𝓝 (c ^ (-1 / θ))) :=
  (tailData_of_regVary ν hθ hT).ratio_tendsto (tailQuantile_tendsto_atTop hθ hT) hc
    ((tailData_of_regVary ν hθ hT).level_ratio_one hc)

/-- (d) `q_{⌊λ n⌋} / q_n → λ ^ (1/θ)`. -/
theorem tailQuantile_floor_div_tailQuantile (hθ : 0 < θ)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) {l : ℝ}
    (hl : 0 < l) :
    Tendsto (fun n : ℕ => tailQuantile ν ⌊l * n⌋₊ / tailQuantile ν n) atTop
      (𝓝 (l ^ (1 / θ))) := by
  have h := tailData_of_regVary ν hθ hT
  have hb := h.level_mul_tail one_pos
  have hm : Tendsto (fun n : ℕ => ⌊l * n⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop l hl
  have hb2 := hb.comp hm
  have hfl : Tendsto (fun n : ℕ => ((⌊l * n⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 l) :=
    (tendsto_nat_floor_mul_div_atTop hl.le).comp tendsto_natCast_atTop_atTop
  have hinv := hfl.inv₀ hl.ne'
  have hlim := (hb2.div hb one_ne_zero).mul hinv
  rw [div_one, one_mul] at hlim
  have hc : 0 < l⁻¹ := inv_pos.2 hl
  have hres := h.ratio_tendsto (tailQuantile_tendsto_atTop hθ hT)
    (r := fun n : ℕ => tailQuantile ν ⌊l * n⌋₊) hc (by
      refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop 0, hm.eventually_gt_atTop 0] with n hn hmn
      simp only [Function.comp, Pi.div_apply, tailQuantile_eq]
      have hn' : (n : ℝ) ≠ 0 := by positivity
      have hm' : ((⌊l * n⌋₊ : ℕ) : ℝ) ≠ 0 := by positivity
      have h1 := (h.pos
        (levelQuantile (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)})
          (1 / ((⌊l * n⌋₊ : ℕ) : ℝ)))).ne'
      have h2 := (h.pos
        (levelQuantile (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)})
          (1 / (n : ℝ)))).ne'
      field_simp)
  rw [Real.inv_rpow hl.le, neg_div, Real.rpow_neg hl.le, inv_inv] at hres
  exact hres

end Measure

end BGW.StableTrees.Attraction.QuantileInversion
