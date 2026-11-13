module

public import BGWLeaves.ClassicalLimits.Defs
public import BGWLeaves.LocalEstimates.Defs
public import BGW.StableTrees.NonmonotoneNorming
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.StableProcessLaw
public import BGW.StableTrees.StableProcessMarkov
public import BGW.StableTrees.StableProcessBrownian
public import BGW.StableTrees.StableProcessNoNegativeJumps
public import BGW.StableTrees.ExcursionLifetimeTail
public import BGW.StableTrees.BrownianPair
public import BGW.StableTrees.VervaatIto
public import BGW.StableTrees.StableBridgeMinimum
public import BGW.StableTrees.StableBridgeClosed
public import BGW.Skorokhod.VervaatRotate
public import BGWLeaves.Coding
public import BGWLeaves.Conditioning.Defs

/-!
# The cited results, restated on BGW's objects

The cited results, restated on BGW's objects. The statements have exactly the types stated in
`BGWLeaves.ClassicalLimits`. The printed-norming version `thm_cv1_printed` uses
`isRealStableAttracted_norming` (`BGWLeaves.Coding`).
-/

@[expose] public section

namespace BGWLeaves.ClassicalLimits.Cited

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- Theorem 4.1 for an arbitrary admissible norming: take the contour marginal of the joint theorem. -/
theorem thm_cv1 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => (DiscreteForest.exactTreeLaw μ (q k)).map
        (ExactContour.treeContourPath B (q k) 1)) atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (ExactContour.tendsto_exactHeightContourLaw_of_attracted hc hne hB hqtop hq) continuous_snd
  have heq (k : ℕ) :
      (ExactContour.exactHeightContourLaw μ B (q k) (hq k)).map Prod.snd =
        (DiscreteForest.exactTreeLaw μ (q k)).map (ExactContour.treeContourPath B (q k) 1) := by
    apply Subtype.ext
    exact Measure.map_map measurable_snd (ExactContour.measurable_heightContourPath B (q k))
  have hseq :
      (fun k => (ExactContour.exactHeightContourLaw μ B (q k) (hq k)).map Prod.snd) =
        (fun k => (DiscreteForest.exactTreeLaw μ (q k)).map
          (ExactContour.treeContourPath B (q k) 1)) :=
    funext heq
  change Tendsto (fun k => (ExactContour.exactHeightContourLaw μ B (q k) (hq k)).map Prod.snd)
    atTop _ at h
  rw [hseq] at h
  have hlim : (((excLaw θ).map (fun p => (p.2, p.2))).map Prod.snd) = (excLaw θ).map Prod.snd := by
    apply Subtype.ext
    change Measure.map _ (Measure.map _ (excLaw θ).toMeasure) =
      Measure.map _ (excLaw θ).toMeasure
    rw [Measure.map_map
      (g := (Prod.snd : C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) →
        C(Set.Icc (0 : ℝ) 1, ℝ)))
      (f := fun p : Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) => (p.2, p.2))
      measurable_snd (by fun_prop)]
    simp only [Function.comp_def]
  rw [hlim] at h
  exact h

/-- Theorem 4.1 in its printed form, with the corrected canonical norming: aperiodicity makes every
large size admissible, so `thm_cv1` along the shifted sequence `k ↦ k + N` gives the full limit. -/
theorem thm_cv1_printed {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (DiscreteForest.exactTreeLaw μ n).map
        (ExactContour.treeContourPath (norming (stepLaw μ) θ) n 1)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  obtain ⟨N, hN⟩ := BGWLeaves.sizeEvent_ne_zero_eventually hc hne hap hDA
  have hB := BGWLeaves.isRealStableAttracted_norming hc hne hDA
  have h := thm_cv1 hc hne hB (q := fun k => k + N) (tendsto_add_atTop_nat N)
    (fun k => hN (k + N) (Nat.le_add_left N k))
  exact (Filter.tendsto_add_atTop_iff_nat N).1 h

/-- The height marginal is definitionally the second coordinate of `excursionPair`. -/
theorem rem_cv1 (θ : ℝ) :
    (excLaw θ).map Prod.snd = (unitExcursionLaw θ).map (fun e => (excursionPair θ 1 e).2) := by
  apply Subtype.ext
  exact Measure.map_map measurable_snd (measurable_excursionPair θ 1)

private theorem height_positive_iff_windows
    (h : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < h t) ↔
      ∀ a b : ℚ, ∀ ha0 : 0 < (a : ℝ), ∀ hab : a ≤ b, ∀ hb : (b : ℝ) < 1,
        Set.MapsTo h
          (Set.Icc
            (⟨a, ha0.le, (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab).trans hb.le⟩ :
              Set.Icc (0 : ℝ) 1)
            (⟨b, ha0.le.trans (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab), hb.le⟩ :
              Set.Icc (0 : ℝ) 1))
          (Set.Ioi 0) := by
  refine ⟨?_, ?_⟩
  · intro hpos a b ha0 hab hb t ht
    exact hpos t (ha0.trans_le ht.1) ((show (t : ℝ) ≤ (b : ℝ) from ht.2).trans_lt hb)
  · intro hpos t ht0 ht1
    obtain ⟨a, ha0, hat⟩ := exists_rat_btwn ht0
    obtain ⟨b, htb, hb1⟩ := exists_rat_btwn ht1
    have hab : a ≤ b := by exact_mod_cast hat.le.trans htb.le
    exact hpos a b ha0 hab hb1 ⟨hat.le, htb.le⟩

private theorem measurableSet_height_pos :
    MeasurableSet {h : C(Set.Icc (0 : ℝ) 1, ℝ) |
      ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < h t} := by
  simp_rw [height_positive_iff_windows, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  apply MeasurableSet.iInter
  intro ha0
  apply MeasurableSet.iInter
  intro hab
  apply MeasurableSet.iInter
  intro hb
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc isOpen_Ioi).measurableSet

private theorem measurableSet_height_endpoints_pos :
    MeasurableSet {h : C(Set.Icc (0 : ℝ) 1, ℝ) |
      h ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ h ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < h t} := by
  have h0 : MeasurableSet {h : C(Set.Icc (0 : ℝ) 1, ℝ) |
      h ⟨0, le_rfl, zero_le_one⟩ = 0} :=
    measurableSet_eq_fun (ContinuousMap.measurable_eval _) measurable_const
  have h1 : MeasurableSet {h : C(Set.Icc (0 : ℝ) 1, ℝ) |
      h ⟨1, zero_le_one, le_rfl⟩ = 0} :=
    measurableSet_eq_fun (ContinuousMap.measurable_eval _) measurable_const
  simpa only [Set.ofPred_and, Set.inter_assoc] using (h0.inter h1).inter measurableSet_height_pos

/-- Endpoints and positivity of the height marginal. -/
theorem height_exc_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ h ∂((excLaw θ).map Prod.snd).toMeasure,
      h ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ h ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < h t := by
  rw [ProbabilityMeasure.toMeasure_map,
    ae_map_iff measurable_snd.aemeasurable measurableSet_height_endpoints_pos]
  exact excLaw_height_endpoints_pos hθ

/-- Laplace transform of the fixed-time stable marginal. -/
theorem sec51_laplace {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (t : Set.Icc (0 : ℝ) T)
    (ht : 0 < (t : ℝ)) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ f, Real.exp (-lam * f t) ∂(stableProcessLaw θ T).toMeasure = Real.exp (t * lam ^ θ) := by
  calc
    _ = ∫ x, Real.exp (-lam * x) ∂((stableProcessLaw θ T : Measure (Skorokhod.D T ℝ)).map
        (fun f => f t)) := (integral_map (Skorokhod.measurable_eval t).aemeasurable
          (by fun_prop)).symm
    _ = _ := by
      rw [map_eval_stableProcessLaw hθ hT t ht]
      exact integral_exp_neg_mul_stableLawAt hθ ht hlam

/-- Stable-process scaling in BGW's path coordinates. -/
theorem sec51_scaling {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) {c : ℝ} (hc : 0 < c) :
    (stableProcessLaw θ (c * T)).map
        (fun f : Skorokhod.D (c * T) ℝ => Skorokhod.timeSpaceScale T (mul_pos hc hT).le
          (f, c ^ (-(1 / θ)), (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ)))) =
      stableProcessLaw θ T := by
  exact stableProcessLaw_scaling hθ hT hc

/-- The fixed-time marginal is the stable-density measure. -/
theorem sec51_density {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (t : Set.Icc (0 : ℝ) T)
    (ht : 0 < (t : ℝ)) :
    (stableProcessLaw θ T : Measure (Skorokhod.D T ℝ)).map (fun f => f t) =
      volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x)) := by
  rw [map_eval_stableProcessLaw hθ hT t ht, stableLawAt_eq_withDensity hθ ht]

/-- The stable process has no negative jumps almost surely. -/
theorem sec51_noNegativeJumps {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : Skorokhod.D T ℝ ∂(stableProcessLaw θ T).toMeasure,
      ∀ t : Set.Icc (0 : ℝ) T, Function.leftLim (f : Set.Icc (0 : ℝ) T → ℝ) t ≤ f t := by
  exact ae_leftLim_le_stableProcessLaw hθ hT

/-- At stability index two, the stable process is Brownian motion scaled by `sqrt 2`. -/
theorem sec51_two_process {T : ℝ} (hT : 0 < T) :
    stableProcessLaw 2 T = ContinuumTrees.BrownianD.wienerD (NNReal.sqrt 2) T := by
  exact stableProcessLaw_two hT

/-- The excursion-lifetime tail is finite and positive. -/
theorem sec51_lifetime_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ} (ht : 0 < t) :
    0 < excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} ∧
      excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} < ⊤ := by
  rw [excursionMeasure_lifetime_tail hθ t ht]
  have hθ0 : 0 < θ := lt_trans zero_lt_one hθ.1
  have ha : 0 < 1 - 1 / θ := sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1)
  have hG : 0 < Real.Gamma (1 - 1 / θ) := Real.Gamma_pos_of_pos ha
  exact ⟨ENNReal.ofReal_pos.mpr (div_pos (Real.rpow_pos_of_pos ht _) hG), ENNReal.ofReal_lt_top⟩

/-- Endpoints and positivity of the normalized Lévy excursion. -/
theorem sec51_exc_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ x : Skorokhod.D 1 ℝ ∂(levyExcLaw θ).toMeasure,
      x ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
        (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < x t) ∧
        x ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim (x : Set.Icc (0 : ℝ) 1 → ℝ) ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  exact levyExcLaw_endpoints_pos hθ

/-- Brownian identification of the excursion/height pair. -/
theorem sec51_two_exc :
    excLaw 2 = ContinuumTrees.VervaatBridge.law.map
      (fun e => (Skorokhod.ofContinuous (T := 1) (Real.sqrt 2 • e), Real.sqrt 2 • e)) := by
  exact BrownianIdentification.excLaw_two

/-- The joint walk/height tail-conditioned limit. -/
theorem thm_cvW {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map (TailPair.treePairPath B n T))
      atTop (𝓝 (tailExcLaw θ T)) := by
  exact TailPair.tendsto_tailPairLaw_of_attracted hc hne hB hT

/-- BGW's `gamma_identity`, projected onto the equality of the two proved integrable integrals. -/
theorem prop_Gamma {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    (F : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ z, |F z| ≤ C) :
    ∫ z, F (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure =
      ∫ z, F (restrictPair ha.2.le z) * gammaA θ a (evalEnd a (restrictPair ha.2.le z).1)
        ∂(tailExcLaw θ 1).toMeasure := by
  exact (gamma_identity hθ a ha F hF hFb).2.2

/-- The project's density is exactly BGW's time-scaled stable density. -/
theorem pDens_eq_stableDensityAt (θ s x : ℝ) : BGWLeaves.pDens θ s x = stableDensityAt θ s x := by
  unfold BGWLeaves.pDens stableDensityAt
  rw [neg_div, mul_comm x]

/-- The project's downward-jump kernel is exactly BGW's. -/
theorem qKernel_eq_kernel (θ s x : ℝ) :
    BGWLeaves.qKernel θ s x = BGW.StableTrees.qKernel θ s x := by
  unfold BGWLeaves.qKernel BGW.StableTrees.qKernel
  rw [pDens_eq_stableDensityAt]

/-- The project's integrated size-biased tail kernel is exactly BGW's. -/
theorem sizeTailKernel_eq_kernel (θ s x : ℝ) :
    BGWLeaves.sizeTailKernel θ s x = BGW.StableTrees.sizeTailKernel θ s x := by
  unfold BGWLeaves.sizeTailKernel BGW.StableTrees.sizeTailKernel
  simp only [qKernel_eq_kernel]

/-- BGW's `gammaA` in the notation of the paper's kernels. -/
theorem gammaA_eq_paper (θ a x : ℝ) :
    gammaA θ a x = θ * BGWLeaves.qKernel θ (1 - a) x / BGWLeaves.sizeTailKernel θ (1 - a) x := by
  unfold gammaA
  rw [qKernel_eq_kernel, sizeTailKernel_eq_kernel]

/-- On paths starting at zero, `vervaatD` is the printed Vervaat rotation. -/
theorem def_vervaatC (f : Skorokhod.D 1 ℝ) (hf0 : f ⟨0, le_rfl, zero_le_one⟩ = 0)
    (t : Set.Icc (0 : ℝ) 1) :
    Skorokhod.vervaatD f t =
      if (Skorokhod.vervaatTime f : ℝ) + t ≤ 1 then
        f (Set.projIcc 0 1 zero_le_one ((Skorokhod.vervaatTime f : ℝ) + t)) - ⨅ s, f s
      else
        f (Set.projIcc 0 1 zero_le_one ((Skorokhod.vervaatTime f : ℝ) + t - 1)) +
          f ⟨1, zero_le_one, le_rfl⟩ - ⨅ s, f s := by
  change (if (Skorokhod.vervaatTime f : ℝ) + t ≤ 1 then
      f (Set.projIcc 0 1 zero_le_one ((Skorokhod.vervaatTime f : ℝ) + t)) - ⨅ s, f s
    else
      f (Set.projIcc 0 1 zero_le_one ((Skorokhod.vervaatTime f : ℝ) + t - 1)) +
        f ⟨1, zero_le_one, le_rfl⟩ - (⨅ s, f s) - f ⟨0, le_rfl, zero_le_one⟩) = _
  rw [hf0, sub_zero]

/-- Continuity of Vervaat and its image under the stable bridge. -/
theorem prop_bridge_i {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (∀ᵐ f ∂(stableBridgeLaw θ).toMeasure, ContinuousAt Skorokhod.vervaatD f) ∧
      (stableBridgeLaw θ).map Skorokhod.vervaatD = levyExcLaw θ := by
  refine ⟨stableBridgeLaw_ae_continuousAt_vervaatD hθ, ?_⟩
  apply Subtype.ext
  exact VervaatIto.map_vervaatD_stableBridgeLaw hθ

/-- The bridge-prefix expectation formula. -/
theorem prop_bridge_ii {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1)
    {F : Skorokhod.D a ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f, F (Skorokhod.restrict ha1.le f) ∂(stableBridgeLaw θ).toMeasure =
      ∫ g, F g * (stableDensityAt θ (1 - a) (-(g ⟨a, ha.le, le_rfl⟩)) /
        Scalar.stableDensity θ 0) ∂(stableProcessLaw θ a).toMeasure := by
  simpa only [bridgePrefixWeight, mul_comm] using
    (integral_restrict_stableBridgeLaw hθ ha ha1 hF hFb)

/-- The discrete Vervaat definitions in the two developments agree. -/
theorem vervaat_eq_rotate_vervaatIndex (x : List ℤ) :
    BGWLeaves.vervaat x = x.rotate (Skorokhod.vervaatIndex x) := by
  unfold BGWLeaves.vervaat BGWLeaves.vervaatIdx Skorokhod.vervaatIndex
  exact BGWLeaves.cyclicShift_eq_rotate x _

end BGWLeaves.ClassicalLimits.Cited
