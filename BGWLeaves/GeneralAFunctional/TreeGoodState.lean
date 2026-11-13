module

public import BGWLeaves.GeneralAFunctional.TreePathLimit
public import BGW.StableTrees.ExactPrefixLimit
public import BGW.Skorokhod.RestrictContinuity

/-! Full-mass continuity states for the augmented tail excursion law. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeGoodState

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreeAugmented
open scoped ENNReal NNReal Topology

theorem continuousAt_of_leftLim_eq {T : ℝ≥0} (f : D (T : ℝ) ℝ)
    (t : Set.Icc (0 : ℝ) T) (ht : Function.leftLim f t = f t) : ContinuousAt f t := by
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (isCadlag f).isRightContinuous _⟩
  change Tendsto f (𝓝[<] t) (𝓝 (f t))
  simpa only [ht] using (isCadlag f).tendsto_nhdsLT_leftLim t

theorem continuousAt_restrictPair {a b : ℝ≥0} (hab : a ≤ b) {z : PairSpace b}
    (hz : ContinuousAt z.1 ⟨a, a.coe_nonneg, hab⟩) : ContinuousAt (restrictPair hab) z := by
  apply ContinuousAt.prodMk
  · exact (Skorokhod.continuousAt_restrict a.coe_nonneg (NNReal.coe_le_coe.mpr hab) hz).comp continuousAt_fst
  · exact (ContinuousMap.continuous_precomp
      ⟨Set.inclusion (Set.Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hab)), continuous_inclusion _⟩).continuousAt.comp
        continuousAt_snd

theorem ae_tail_pair_leftLim {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) :
    ∀ᵐ z ∂(tailExcLaw θ b).toMeasure,
      Function.leftLim z.1 ⟨a, a.coe_nonneg, hab⟩ = z.1 ⟨a, a.coe_nonneg, hab⟩ := by
  let t : Icc (0 : ℝ) b := ⟨a, a.coe_nonneg, hab⟩
  change ∀ᵐ z ∂((tailExcursionLaw θ).toMeasure.map (excursionPair θ b)), _
  apply (ae_map_iff (measurable_excursionPair θ b).aemeasurable
    (measurableSet_eq_fun ((measurable_leftLim_eval t).comp measurable_fst)
      ((measurable_eval t).comp measurable_fst))).mpr
  rw [coe_tailExcursionLaw hθ, tailExcursionMeasure]
  apply Measure.ae_smul_measure
  have hh := ae_restrict_of_ae (s := {e : Excursion | (1 : ℝ) < (e.lifetime : ℝ)})
    (N_noFixedJump hθ a ha)
  filter_upwards [hh] with e he
  change Function.leftLim (excursionRestrict b e) t = excursionRestrict b e t
  rw [leftLim_excursionRestrict b a ha hab]
  exact he

def goodState {a b : ℝ≥0} (hab : a ≤ b) : Set (PairSpace b × ℝ) :=
  {z | Function.leftLim z.1.1 ⟨b, b.coe_nonneg, le_rfl⟩ = z.1.1 ⟨b, b.coe_nonneg, le_rfl⟩ ∧
    0 < DiscreteBridge.endValue b z.1.1 ∧ z.2 = b ∧
    Function.leftLim z.1.1 ⟨a, a.coe_nonneg, hab⟩ = z.1.1 ⟨a, a.coe_nonneg, hab⟩}

theorem measurableSet_goodState {a b : ℝ≥0} (hab : a ≤ b) : MeasurableSet (goodState hab) := by
  have hf : Measurable (fun z : PairSpace b × ℝ => z.1.1) := measurable_fst.comp measurable_fst
  exact (measurableSet_eq_fun ((measurable_leftLim_eval _).comp hf) ((measurable_eval _).comp hf)).inter
    ((measurableSet_lt measurable_const ((measurable_eval _).comp hf)).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).inter
        (measurableSet_eq_fun ((measurable_leftLim_eval _).comp hf) ((measurable_eval _).comp hf))))

theorem ae_goodState {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a b : ℝ≥0}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ z ∂(augmentedTailLimit θ b).toMeasure, z ∈ goodState hab := by
  have hfst : (tailExcLaw θ b).toMeasure.map Prod.fst = (PathTail.tailPrefixLimit θ b).toMeasure :=
    congrArg ProbabilityMeasure.toMeasure (tailExcLaw_map_fst θ b)
  have hpos : ∀ᵐ z ∂(tailExcLaw θ b).toMeasure, 0 < DiscreteBridge.endValue b z.1 := by
    have hh := (ExactPrefix.ae_tailPrefix_continuousAt_pos hθ b hb).mono fun _ h => h.2
    rw [← hfst] at hh
    exact ae_of_ae_map measurable_fst.aemeasurable hh
  change ∀ᵐ z ∂((tailExcLaw θ b).toMeasure.map (fun z => (z, (b : ℝ)))), z ∈ goodState hab
  apply (ae_map_iff (measurable_id.prodMk measurable_const).aemeasurable (measurableSet_goodState hab)).mpr
  filter_upwards [ae_tail_pair_leftLim hθ hb.1 le_rfl, hpos, ae_tail_pair_leftLim hθ ha hab]
    with z hz hp hza
  exact ⟨hz, hp, rfl, hza⟩

end BGWLeaves.GeneralAFunctional.TreeGoodState
