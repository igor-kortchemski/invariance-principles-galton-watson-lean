module

public import BGWLeaves.ClassicalLimits.Defs
public import BGW.Probability.WeakConvergence
public import BGW.StableTrees.JointExcursion

/-!
# M12 provider `Perturbation`

Provider for Lemma 5.7 (random time and space perturbation).  It will provide the registered holes
`lem_CVproba` and `lem_CVproba_pair` of `BGWLeaves.ClassicalLimits`, exported in namespace
`BGWLeaves.ClassicalLimits.Perturbation` with exactly the types of the statements file.
-/

@[expose] public section

namespace BGWLeaves.ClassicalLimits.Perturbation

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees
open scoped Topology NNReal

set_option maxHeartbeats 200000 in
/-- Two successive applications of Slutsky, followed by continuous mapping. -/
private theorem perturb_mapping
    {X A Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [PseudoMetricSpace A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Z : ∀ n, Ω n → X) (K : ∀ n, Ω n → A)
    (S : ∀ n, Ω n → Set.Ioi (0 : ℝ))
    (hZm : ∀ n, Measurable (Z n)) (hKm : ∀ n, Measurable (K n))
    (hSm : ∀ n, Measurable (fun ω => (S n ω : ℝ)))
    (L : ProbabilityMeasure X) (c : A)
    (hZ : Tendsto (fun n => (P n).map (Z n)) atTop (𝓝 L))
    (hK : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (K n ω) c}) atTop (𝓝 0))
    (hS : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (S n ω : ℝ) 1}) atTop (𝓝 0))
    (F : X × A × Set.Ioi (0 : ℝ) → Y) (hF : Measurable F)
    (hcont : ∀ᵐ x ∂L.toMeasure, ContinuousAt F (x, c, ⟨1, one_pos⟩)) :
    Tendsto (fun n => (P n).map (fun ω => F (Z n ω, K n ω, S n ω))) atTop
      (𝓝 (L.map (fun x => F (x, c, ⟨1, one_pos⟩)))) := by
  let j : X → X × A := fun x => (x, c)
  let k : X × A → (X × A) × Set.Ioi (0 : ℝ) := fun x => (x, ⟨1, one_pos⟩)
  let r : (X × A) × Set.Ioi (0 : ℝ) → X × A × Set.Ioi (0 : ℝ) :=
    fun x => (x.1.1, x.1.2, x.2)
  have hj : Measurable j := measurable_id.prodMk measurable_const
  have hk : Measurable k := measurable_id.prodMk measurable_const
  have hr : Continuous r := continuous_fst.fst.prodMk
    (continuous_fst.snd.prodMk continuous_snd)
  have hSm' : ∀ n, Measurable (S n) := fun n => (hSm n).subtype_mk
  have hZK : Tendsto (fun n => (P n).map (fun ω => (Z n ω, K n ω))) atTop
      (𝓝 (L.map j)) :=
    BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error P hZm hKm hZ hK
  have hZKS : Tendsto (fun n => (P n).map (fun ω => ((Z n ω, K n ω), S n ω)))
      atTop (𝓝 ((L.map j).map k)) :=
    BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error P
      (fun n => (hZm n).prodMk (hKm n)) hSm' hZK hS
  have hc : ∀ᵐ x ∂((L.map j).map k).toMeasure, ContinuousAt (F ∘ r) x := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hk.aemeasurable
      (IsGδ.setOfPred_continuousAt (F ∘ r)).measurableSet).mpr
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hj.aemeasurable
      ((IsGδ.setOfPred_continuousAt (F ∘ r)).measurableSet.preimage hk)).mpr
    filter_upwards [hcont] with x hx
    exact ContinuousAt.comp (f := r) hx hr.continuousAt
  have hm := BGW.Probability.tendsto_map_of_ae_continuousAt hZKS
    (fun _ => (hF.comp hr.measurable).aemeasurable) hc
  have hseq (n : ℕ) :
      ((P n).map (fun ω => ((Z n ω, K n ω), S n ω))).map (F ∘ r) =
        (P n).map (fun ω => F (Z n ω, K n ω, S n ω)) := by
    apply Subtype.ext
    exact Measure.map_map (hF.comp hr.measurable)
      (((hZm n).prodMk (hKm n)).prodMk (hSm' n))
  have hlim : ((L.map j).map k).map (F ∘ r) =
      L.map (fun x => F (x, c, ⟨1, one_pos⟩)) := by
    apply Subtype.ext
    change (L.toMeasure.map j |>.map k).map (F ∘ r) = _
    rw [Measure.map_map (hF.comp hr.measurable) hk,
      Measure.map_map ((hF.comp hr.measurable).comp hk) hj]
    rfl
  simpa only [hseq, hlim] using hm

theorem lem_CVproba {E : Type*} [NormedRing E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {T a : ℝ} (ha : 0 < a) (haT : a < T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, ProbabilityMeasure (Ω n))
    (Z : ∀ n, Ω n → Skorokhod.D T E) (K : ∀ n, Ω n → E) (S : ∀ n, Ω n → Set.Ioi (0 : ℝ))
    (hZm : ∀ n, Measurable (Z n)) (hKm : ∀ n, Measurable (K n))
    (hSm : ∀ n, Measurable (fun ω => ((S n ω : ℝ))))
    (L : ProbabilityMeasure (Skorokhod.D T E))
    (hZ : Tendsto (fun n => (P n).map (Z n)) atTop (𝓝 L))
    (hcont : ∀ᵐ f : Skorokhod.D T E ∂L.toMeasure,
      ContinuousAt (f : Set.Icc (0 : ℝ) T → E) ⟨a, ha.le, haT.le⟩)
    (hK : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (K n ω) 1}) atTop (𝓝 0))
    (hS : ∀ ε > 0,
      Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist ((S n ω : ℝ)) 1}) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).map (fun ω =>
        Skorokhod.timeSpaceScale a (ha.le.trans haT.le) (Z n ω, K n ω, S n ω)))
      atTop (𝓝 (L.map (Skorokhod.restrict haT.le))) := by
  have hm := perturb_mapping P Z K S hZm hKm hSm L 1 hZ hK hS
    (Skorokhod.timeSpaceScale a (ha.le.trans haT.le))
    (measurable_timeSpaceScale a _) (hcont.mono fun f hf =>
      Skorokhod.continuousAt_timeSpaceScale ha haT hf)
  have heq : (fun f : Skorokhod.D T E => Skorokhod.timeSpaceScale a
      (ha.le.trans haT.le) (f, 1, ⟨1, one_pos⟩)) = Skorokhod.restrict haT.le := by
    funext f
    apply Skorokhod.ext
    intro t
    change 1 * f _ = f _
    rw [one_mul]
    congr 1
    apply Subtype.ext
    simp only [one_mul, min_eq_left (t.2.2.trans haT.le)]
  simpa only [heq] using hm

theorem lem_CVproba_pair {T a : ℝ≥0} (ha : 0 < a) (haT : a < T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, ProbabilityMeasure (Ω n))
    (Z : ∀ n, Ω n → Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ))
    (K : ∀ n, Ω n → ℝ × ℝ) (S : ∀ n, Ω n → Set.Ioi (0 : ℝ))
    (hZm : ∀ n, Measurable (Z n)) (hKm : ∀ n, Measurable (K n))
    (hSm : ∀ n, Measurable (fun ω => ((S n ω : ℝ))))
    (L : ProbabilityMeasure (Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)))
    (hZ : Tendsto (fun n => (P n).map (Z n)) atTop (𝓝 L))
    (hcont : ∀ᵐ z : Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) ∂L.toMeasure,
      ContinuousAt (z.1 : Set.Icc (0 : ℝ) T → ℝ)
        ⟨(a : ℝ), a.coe_nonneg, NNReal.coe_le_coe.2 haT.le⟩)
    (hK : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (K n ω) 1}) atTop (𝓝 0))
    (hS : ∀ ε > 0,
      Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist ((S n ω : ℝ)) 1}) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).map (fun ω =>
        (Skorokhod.timeSpaceScale (a : ℝ) T.coe_nonneg ((Z n ω).1, (K n ω).1, S n ω),
          Skorokhod.timeSpaceScaleC (a : ℝ) T.coe_nonneg ((Z n ω).2, (K n ω).2, S n ω))))
      atTop (𝓝 (L.map (restrictPair haT.le))) := by
  let F := fun p : (Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) ×
      (ℝ × ℝ) × Set.Ioi (0 : ℝ) =>
    (Skorokhod.timeSpaceScale (a : ℝ) T.coe_nonneg (p.1.1, p.2.1.1, p.2.2),
      Skorokhod.timeSpaceScaleC (a : ℝ) T.coe_nonneg (p.1.2, p.2.1.2, p.2.2))
  have hF : Measurable F :=
    ((measurable_timeSpaceScale (a : ℝ) T.coe_nonneg).comp
      (measurable_fst.fst.prodMk (measurable_snd.fst.fst.prodMk measurable_snd.snd))).prodMk
    ((measurable_timeSpaceScaleC (a : ℝ) T.coe_nonneg).comp
      (measurable_fst.snd.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd)))
  have hc : ∀ᵐ z ∂L.toMeasure, ContinuousAt F (z, 1, ⟨1, one_pos⟩) := by
    filter_upwards [hcont] with z hz
    let r₁ := fun p : (Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) ×
        (ℝ × ℝ) × Set.Ioi (0 : ℝ) => (p.1.1, p.2.1.1, p.2.2)
    let r₂ := fun p : (Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) ×
        (ℝ × ℝ) × Set.Ioi (0 : ℝ) => (p.1.2, p.2.1.2, p.2.2)
    have hr₁ : Continuous r₁ := continuous_fst.fst.prodMk
      (continuous_snd.fst.fst.prodMk continuous_snd.snd)
    have hr₂ : Continuous r₂ := continuous_fst.snd.prodMk
      (continuous_snd.fst.snd.prodMk continuous_snd.snd)
    exact (ContinuousAt.comp (f := r₁) (x := (z, (1 : ℝ × ℝ), (⟨1, one_pos⟩ : Set.Ioi (0 : ℝ))))
      (Skorokhod.continuousAt_timeSpaceScale (NNReal.coe_pos.mpr ha)
        (NNReal.coe_lt_coe.mpr haT) hz) hr₁.continuousAt).prodMk
      (ContinuousAt.comp (f := r₂) (x := (z, (1 : ℝ × ℝ), (⟨1, one_pos⟩ : Set.Ioi (0 : ℝ))))
        (Skorokhod.continuous_timeSpaceScaleC (a : ℝ) T.coe_nonneg).continuousAt
        hr₂.continuousAt)
  have hm := perturb_mapping P Z K S hZm hKm hSm L 1 hZ hK hS F hF hc
  have heq : (fun z => F (z, 1, ⟨1, one_pos⟩)) = restrictPair haT.le := by
    funext z
    apply Prod.ext
    · apply Skorokhod.ext
      intro t
      change 1 * z.1 _ = z.1 _
      rw [one_mul]
      congr 1
      apply Subtype.ext
      simp only [one_mul, min_eq_left (t.2.2.trans (NNReal.coe_le_coe.mpr haT.le))]
    · apply ContinuousMap.ext
      intro t
      change 1 * z.2 _ = z.2 _
      rw [one_mul]
      congr 1
      apply Subtype.ext
      simp only [one_mul, min_eq_left (t.2.2.trans (NNReal.coe_le_coe.mpr haT.le))]
      rfl
  simpa only [heq] using hm

end BGWLeaves.ClassicalLimits.Perturbation
