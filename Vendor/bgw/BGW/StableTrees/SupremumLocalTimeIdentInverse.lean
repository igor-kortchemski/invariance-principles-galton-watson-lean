/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdentPath
public import BGW.StableTrees.SupremumLocalTimeIdentHitting

/-!
# Inversion of the public supremum clock

The real clock discards infinite extended values. Its strict inverse therefore requires a
boundary test at the common hitting and blow-up time, even though blow-up is almost surely absent.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Inverse local time `A_z = inf{t | M_t > z}`. -/
noncomputable def supLocalTimeInverse (θ : ℝ) (f : DLoc) (z : ℝ≥0) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (z : ℝ) < supLocalTime θ f u}

/-- Ladder time `A_z` (finite reading, junk `0` on `⊤`). -/
noncomputable def supLadderTime (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (supLocalTimeInverse θ f z).untopD 0

/-- Ladder height `B_z = S_{A_z}`. -/
noncomputable def supLadderHeight (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ :=
  supRunning f (supLadderTime θ z f)

open scoped Classical in
/-- The explicit measurable representative of the public inverse: `a` if `a < b`, or if
`a = b < ⊤` and `z < p(a) < ⊤` (isolated finite crossing at blow-up); `⊤` otherwise. -/
noncomputable def supInverseRep (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0∞ :=
  if supHitting θ z f < supBlowup θ f ∨
      (supHitting θ z f = supBlowup θ f ∧ supHitting θ z f < ⊤ ∧
        (z : ℝ≥0∞) < supLocalTimeENN θ f (supHitting θ z f).toNNReal ∧
        supLocalTimeENN θ f (supHitting θ z f).toNNReal < ⊤)
  then supHitting θ z f else ⊤

private theorem inf_finite_crossing {p : ℝ≥0 → ℝ≥0∞} (hp : Monotone p) (z : ℝ≥0) :
    (⨅ t : ℝ≥0, if (z : ℝ≥0∞) < p t ∧ p t < ⊤ then (t : ℝ≥0∞) else ⊤) =
      let a := ⨅ t : ℝ≥0, if (z : ℝ≥0∞) < p t then (t : ℝ≥0∞) else ⊤
      let b := ⨅ t : ℝ≥0, if p t = ⊤ then (t : ℝ≥0∞) else ⊤
      if a < b ∨ (a = b ∧ a < ⊤ ∧ (z : ℝ≥0∞) < p a.toNNReal ∧
        p a.toNNReal < ⊤) then a else ⊤ := by
  classical
  let a : ℝ≥0∞ := ⨅ t : ℝ≥0, if (z : ℝ≥0∞) < p t then (t : ℝ≥0∞) else ⊤
  let b : ℝ≥0∞ := ⨅ t : ℝ≥0, if p t = ⊤ then (t : ℝ≥0∞) else ⊤
  let c : ℝ≥0∞ := ⨅ t : ℝ≥0,
    if (z : ℝ≥0∞) < p t ∧ p t < ⊤ then (t : ℝ≥0∞) else ⊤
  change c = if a < b ∨ (a = b ∧ a < ⊤ ∧ (z : ℝ≥0∞) < p a.toNNReal ∧
    p a.toNNReal < ⊤) then a else ⊤
  have ha (t : ℝ≥0) (ht : (z : ℝ≥0∞) < p t) : a ≤ t :=
    iInf_le_of_le t (by simp only [ite_eq_left ht]; exact le_rfl)
  have hb (t : ℝ≥0) (ht : p t = ⊤) : b ≤ t :=
    iInf_le_of_le t (by simp only [ite_eq_left ht]; exact le_rfl)
  have hc (t : ℝ≥0) (ht : (z : ℝ≥0∞) < p t ∧ p t < ⊤) : c ≤ t :=
    iInf_le_of_le t (by simp only [ite_eq_left ht]; exact le_rfl)
  have hac : a ≤ c := by
    apply le_iInf
    intro t
    split_ifs with ht
    · exact ha t ht.1
    · exact le_top
  have htb (t : ℝ≥0) (ht : p t < ⊤) : (t : ℝ≥0∞) ≤ b := by
    apply le_iInf
    intro u
    split_ifs with hu
    · have htu : t ≤ u := by
        by_contra h
        have hh := hp (le_of_not_ge h)
        rw [hu] at hh
        exact (not_le_of_gt ht) hh
      exact ENNReal.coe_le_coe.mpr htu
    · exact le_top
  have hcross (t : ℝ≥0) (ht : a < t) : (z : ℝ≥0∞) < p t := by
    obtain ⟨u, hu⟩ := iInf_lt_iff.mp ht
    split_ifs at hu with hzu
    · exact hzu.trans_le (hp (ENNReal.coe_lt_coe.mp hu).le)
    · exact (not_lt_of_ge le_top hu).elim
  have hfinite (t : ℝ≥0) (ht : (t : ℝ≥0∞) < b) : p t < ⊤ := by
    exact lt_top_iff_ne_top.mpr (fun h => not_le_of_gt ht (hb t h))
  by_cases hab : a < b
  · rw [ite_eq_left (Or.inl hab)]
    apply le_antisymm _ hac
    apply le_of_forall_gt
    intro r har
    obtain ⟨t, hat, htr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_min hab har)
    exact (hc t ⟨hcross t hat, hfinite t (htr.trans_le (min_le_left _ _))⟩).trans_lt
      (htr.trans_le (min_le_right _ _))
  · by_cases hboundary : a = b ∧ a < ⊤ ∧ (z : ℝ≥0∞) < p a.toNNReal ∧
        p a.toNNReal < ⊤
    · rw [ite_eq_left (Or.inr hboundary)]
      apply le_antisymm _ hac
      exact (hc a.toNNReal ⟨hboundary.2.2.1, hboundary.2.2.2⟩).trans_eq
        (ENNReal.coe_toNNReal hboundary.2.1.ne)
    · rw [ite_eq_right (not_or.mpr ⟨hab, hboundary⟩)]
      apply top_unique
      apply le_iInf
      intro t
      split_ifs with ht
      · have hat : a ≤ (t : ℝ≥0∞) := ha t ht.1
        have hbt : b ≤ (t : ℝ≥0∞) := (le_of_not_gt hab).trans hat
        have htb' := htb t ht.2
        have hbe : b = (t : ℝ≥0∞) := le_antisymm hbt htb'
        have hae : a = (t : ℝ≥0∞) := le_antisymm hat (hbe ▸ le_of_not_gt hab)
        apply False.elim
        apply hboundary
        refine ⟨hae.trans hbe.symm, hae ▸ ENNReal.coe_lt_top, ?_, ?_⟩
        · simpa only [hae, ENNReal.toNNReal_coe] using ht.1
        · simpa only [hae, ENNReal.toNNReal_coe] using ht.2
      · exact le_rfl

private theorem coe_inverse_eq_iInf (θ : ℝ) (f : DLoc) (z : ℝ≥0) :
    (supLocalTimeInverse θ f z : ℝ≥0∞) =
      ⨅ t : ℝ≥0, if (z : ℝ) < supLocalTime θ f t then (t : ℝ≥0∞) else ⊤ := by
  classical
  change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, t = u ∧ (z : ℝ) < supLocalTime θ f u} = _
  apply le_antisymm
  · apply le_iInf
    intro t
    split_ifs with ht
    · exact sInf_le ⟨t, rfl, ht⟩
    · exact le_top
  · apply le_sInf
    rintro t ⟨u, rfl, hu⟩
    exact iInf_le_of_le u (by simp only [ite_eq_left hu]; exact le_rfl)

/-- The raw inverse equals its explicit representative on every path, including blow-up paths. -/
theorem supLocalTimeInverse_eq_rep (θ : ℝ) (f : DLoc) (z : ℝ≥0) :
    (supLocalTimeInverse θ f z : ℝ≥0∞) = supInverseRep θ z f := by
  classical
  rw [coe_inverse_eq_iInf]
  have he (t : ℝ≥0) : (z : ℝ) < supLocalTime θ f t ↔
      (z : ℝ≥0∞) < supLocalTimeENN θ f t ∧ supLocalTimeENN θ f t < ⊤ := by
    rw [supLocalTime_eq_toReal]
    by_cases ht : supLocalTimeENN θ f t = ⊤
    · simp only [ht, ENNReal.toReal_top, lt_self_iff_false, and_false, iff_false]
      exact not_lt_of_ge z.coe_nonneg
    · rw [and_iff_left (lt_top_iff_ne_top.mpr ht),
        ← ENNReal.ofReal_lt_iff_lt_toReal z.coe_nonneg ht, ENNReal.ofReal_coe_nnreal]
  simp_rw [he]
  exact inf_finite_crossing (monotone_supLocalTimeENN θ f) z

/-- The explicit inverse representative is jointly measurable. -/
theorem measurable_supInverseRep_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supInverseRep θ p.1 p.2) := by
  classical
  have ha := measurable_supHitting_uncurry θ
  have hb : Measurable (fun p : ℝ≥0 × DLoc => supBlowup θ p.2) :=
    (measurable_supBlowup θ).comp measurable_snd
  have hp := (measurable_supLocalTimeENN_uncurry θ).comp
    (ha.ennreal_toNNReal.prodMk measurable_snd)
  apply Measurable.ite _ ha measurable_const
  exact (measurableSet_lt ha hb).union ((measurableSet_eq_fun ha hb).inter
    ((measurableSet_lt ha measurable_const).inter
      ((measurableSet_lt (by fun_prop) hp).inter (measurableSet_lt hp measurable_const))))

/-- Joint measurability of the raw public inverse in its extended reading. -/
theorem measurable_supLocalTimeInverse_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => (supLocalTimeInverse θ p.2 p.1 : ℝ≥0∞)) := by
  simp_rw [supLocalTimeInverse_eq_rep]
  exact measurable_supInverseRep_uncurry θ

/-- Everywhere joint measurability of both public ladder processes. -/
theorem measurable_supLadder_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLadderTime θ p.1 p.2) ∧
      Measurable (fun p : ℝ≥0 × DLoc => supLadderHeight θ p.1 p.2) := by
  have hA : Measurable (fun p : ℝ≥0 × DLoc => supLadderTime θ p.1 p.2) :=
    (measurable_supLocalTimeInverse_uncurry θ).ennreal_toNNReal
  exact ⟨hA, measurable_supRunning_uncurry.comp (hA.prodMk measurable_snd)⟩

/-- For an everywhere finite extended clock, its strict hitting time equals the raw inverse. -/
theorem supHitting_eq_inverse_of_finite (θ : ℝ) (f : DLoc) (z : ℝ≥0)
    (hfin : ∀ t, supLocalTimeENN θ f t ≠ ⊤) :
    supHitting θ z f = (supLocalTimeInverse θ f z : ℝ≥0∞) := by
  classical
  rw [coe_inverse_eq_iInf]
  change (⨅ t : ℝ≥0, if (z : ℝ≥0∞) < supLocalTimeENN θ f t then
    (t : ℝ≥0∞) else ⊤) = _
  apply iInf_congr
  intro t
  simp only [supLocalTime_eq_toReal, ← ENNReal.ofReal_lt_iff_lt_toReal z.coe_nonneg (hfin t),
    ENNReal.ofReal_coe_nnreal]

/-- The stopping representative agrees almost surely with the public inverse at each level. -/
theorem ae_supHitting_eq_inverse {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supHitting θ z f = (supLocalTimeInverse θ f z : ℝ≥0∞) := by
  filter_upwards [ae_supLocalTimeENN_eq_aux hθ] with f hf
  exact supHitting_eq_inverse_of_finite θ f z (fun t => by
    rw [hf t]; exact ENNReal.ofReal_ne_top)

/-- The inverse admits an almost surely equal stopping-time representative. -/
theorem exists_isStoppingTime_supLocalTimeInverse {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ τ : DLoc → ℝ≥0∞, IsStoppingTime DLoc.filtration τ ∧
      ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f = (supLocalTimeInverse θ f z : ℝ≥0∞) := by
  exact ⟨supHitting θ z, isStoppingTime_supHitting θ z, ae_supHitting_eq_inverse hθ z⟩

end BGW.StableTrees
