module

public import BGWLeaves.GeneralAFunctional.TreeGoodState
public import BGW.StableTrees.GammaIdentity

/-! The limiting augmented density preserves the joint excursion coupling. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeLimitWeight

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreeAugmented BGWLeaves.GeneralAFunctional.TreeGoodState
open scoped ENNReal NNReal Topology

noncomputable def limitWeight (θ : ℝ) (b : ℝ≥0) (z : PairSpace b × ℝ) : ℝ :=
  max (gammaA θ b (DiscreteBridge.endValue b z.1.1)) 0

theorem measurable_limitWeight (θ : ℝ) (b : ℝ≥0) : Measurable (limitWeight θ b) :=
  (((measurable_gammaA θ).comp (measurable_const.prodMk
    ((measurable_eval _).comp (measurable_fst.comp measurable_fst)))).max measurable_const)

theorem limitWeight_nonneg (θ : ℝ) (b : ℝ≥0) (z : PairSpace b × ℝ) : 0 ≤ limitWeight θ b z :=
  le_max_right _ _

theorem augmentedTailLimit_map_walk (θ : ℝ) (b : ℝ≥0) :
    (augmentedTailLimit θ b).toMeasure.map (fun z => z.1.1) = (PathTail.tailPrefixLimit θ b).toMeasure := by
  rw [augmentedTailLimit, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (f := fun z : PairSpace b => (z, (b : ℝ)))
      (g := fun z : PairSpace b × ℝ => z.1.1)
      (measurable_fst.comp measurable_fst) (measurable_id.prodMk measurable_const)]
  exact congrArg ProbabilityMeasure.toMeasure (tailExcLaw_map_fst θ b)

theorem limitWeight_eq_ae {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {b : ℝ≥0}
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) :
    limitWeight θ b =ᵐ[(augmentedTailLimit θ b).toMeasure]
      (fun z => gammaA θ b (DiscreteBridge.endValue b z.1.1)) := by
  filter_upwards [ae_goodState hθ hb.1 (le_refl b) hb] with z hz
  exact max_eq_left (gammaA_nonneg hθ hb.2 hz.2.1)

theorem integral_limitWeight {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {b : ℝ≥0}
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) :
    ∫ z, limitWeight θ b z ∂(augmentedTailLimit θ b).toMeasure = 1 := by
  rw [integral_congr_ae (limitWeight_eq_ae hθ hb)]
  have hm := (integral_gammaA_tail_eq_one hθ b hb).2
  change (∫ x, gammaA θ b (DiscreteBridge.endValue b x) ∂(PathTail.tailPrefixLimit θ b).toMeasure) = 1 at hm
  rw [← augmentedTailLimit_map_walk θ b,
    integral_map (φ := fun z : PairSpace b × ℝ => z.1.1)
      (f := fun x : D (b : ℝ) ℝ => gammaA θ b (DiscreteBridge.endValue b x))
      (measurable_fst.comp measurable_fst).aemeasurable
      (((measurable_gammaA θ).comp (measurable_const.prodMk (measurable_eval _))).aestronglyMeasurable)] at hm
  exact hm

theorem integral_limitWeight_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (hab : a ≤ b) (hb : b ∈ Ioo (0 : ℝ≥0) 1)
    (F : BoundedContinuousFunction (PairSpace a) ℝ) :
    (∫ z, F (restrictPair hab z.1) * limitWeight θ b z ∂(augmentedTailLimit θ b).toMeasure) =
      ∫ z, F z ∂((excLaw θ).map (restrictPair (hab.trans hb.2.le))).toMeasure := by
  have hb0 : 0 < b := hb.1
  have hb1 : b < 1 := hb.2
  let F' : PairSpace b → ℝ := fun z => F (restrictPair hab z)
  have hFm : Measurable F' := F.continuous.measurable.comp (measurable_restrictPair hab)
  have hFb : ∃ C : ℝ, ∀ z, |F' z| ≤ C :=
    ⟨‖F‖, fun z => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (restrictPair hab z)⟩
  have hgamma := (gamma_identity hθ b hb F' hFm hFb).2.2
  rw [integral_congr_ae ((limitWeight_eq_ae hθ hb).mono fun z hz => by rw [hz])]
  change (∫ z, F' z.1 * gammaA θ b (DiscreteBridge.endValue b z.1.1)
    ∂((tailExcLaw θ b).toMeasure.map (fun z => (z, (b : ℝ)))) ) = _
  rw [integral_map (φ := fun z : PairSpace b => (z, (b : ℝ)))
    (f := fun z : PairSpace b × ℝ => F' z.1 * gammaA θ b (DiscreteBridge.endValue b z.1.1))
    (measurable_id.prodMk measurable_const).aemeasurable
    ((hFm.comp measurable_fst).mul
      ((measurable_gammaA θ).comp (measurable_const.prodMk
        ((measurable_eval _).comp (measurable_fst.comp measurable_fst))))).aestronglyMeasurable]
  dsimp only
  have hproj := congrArg ProbabilityMeasure.toMeasure (tailExcLaw_map_restrictPair θ hb1.le)
  rw [← hproj, ProbabilityMeasure.toMeasure_map,
    integral_map (φ := restrictPair hb1.le)
      (f := fun z : PairSpace b => F' z * gammaA θ b (DiscreteBridge.endValue b z.1))
      (measurable_restrictPair hb1.le).aemeasurable
      (hFm.mul ((measurable_gammaA θ).comp
        (measurable_const.prodMk ((measurable_eval _).comp measurable_fst)))).aestronglyMeasurable]
  erw [← hgamma]
  erw [ProbabilityMeasure.toMeasure_map,
    integral_map (φ := restrictPair (hab.trans hb1.le)) (f := F)
      (measurable_restrictPair (hab.trans hb1.le)).aemeasurable F.continuous.aestronglyMeasurable]
  rfl

end BGWLeaves.GeneralAFunctional.TreeLimitWeight
