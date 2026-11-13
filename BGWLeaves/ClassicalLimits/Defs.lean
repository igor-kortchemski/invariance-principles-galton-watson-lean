module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.Vervaat.Defs
public import BGW.Skorokhod.Scaling
public import BGW.Skorokhod.ScalingContinuous
public import BGW.Skorokhod.Measurable
public import BGW.Skorokhod.MeasurableCylinders
public import BGW.Skorokhod.ExitPartition
public import BGW.StableTrees.WalkPathTightness
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Tranche 2, package M12 `ClassicalLimits`: definitions and proved bridges

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex`): Lemma 5.7 (`lem:CVproba`,
line 1487) and Lemma 6.2(ii) (`lem:CVf2`, line 2009, notation of line 1999).

This file contains the definitions of package M12 (the random walk of Proposition 1.4 and its leaf clock
`T_u`) and the PROVED measurability bridges for the maps pushed forward in the statements of
`BGWLeaves.ClassicalLimits`: the joint time-space scaling of Lemma 5.7 (`measurable_timeSpaceScale`,
`measurable_timeSpaceScaleC`) and the path of Lemma 6.2(ii) (`measurable_leafClockPath`).  No proof
hole, no axiom.  It will be frozen whole.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## Definitions (Lemma 6.2(ii)) -/

/-- The law of the walk of Proposition 1.4 (steps `ω i - 1`, `ω i ∼ μ` i.i.d.) as a probability
measure (tranche 1's `iidWalk μ`). -/
noncomputable def walkLawPM (μ : PMF ℕ) : ProbabilityMeasure (ℕ → ℕ) :=
  ⟨iidWalk μ, by unfold iidWalk; infer_instance⟩

/-- The real increments `ω i - 1` of the walk. -/
noncomputable def walkIncr (ω : ℕ → ℕ) : ℕ → ℝ := fun i => (ω i : ℝ) - 1

/-- `T_u = inf{k : Λ(k) = ⌊u⌋}` (line 1999) as a natural number (junk `0` if `T_u = ∞`, a null event
for `μ 0 ≠ 0`, tranche 1's `walkLeafTime_ne_top_ae`). -/
noncomputable def leafClock (ω : ℕ → ℕ) (u : ℝ) : ℕ := (walkLeafTime ω ⌊u⌋₊).toNat

/-- `(W_{⌊(t/a) T_{an}⌋} / B_{⌊n/μ₀⌋})_{0 ≤ t ≤ a}` of Lemma 6.2(ii), as an element of `D([0,a])`
(the step path on `[0,1]` at time scale `T_{an}`, time-changed by `t ↦ t/a`). -/
noncomputable def leafClockPath (μ0 : ℝ) (B : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (ω : ℕ → ℕ) : Skorokhod.D a ℝ :=
  Skorokhod.timeSpaceScale a zero_le_one
    (Skorokhod.realStepPath 1 (leafClock ω (a * n)) (B ⌊(n : ℝ) / μ0⌋₊) (walkIncr ω), 1,
      ⟨1 / a, Set.mem_Ioi.mpr (one_div_pos.mpr ha)⟩)

/-! ## A piecewise principle -/

/-- If `g` is a measurable integer-valued map and every `G k` is measurable, then
`x ↦ G (g x) x` is measurable (countable partition by the value of `g`). -/
theorem measurable_comp_nat {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {g : X → ℕ} (hg : Measurable g) {G : ℕ → X → Z} (hG : ∀ k, Measurable (G k)) :
    Measurable (fun x => G (g x) x) := by
  intro s hs
  have he : (fun x => G (g x) x) ⁻¹' s = ⋃ k, g ⁻¹' {k} ∩ G k ⁻¹' s := by
    ext x
    simp
  rw [he]
  exact MeasurableSet.iUnion fun k => (hg (measurableSet_singleton k)).inter (hG k hs)

/-! ## The walk leaf clock -/

private theorem measurable_walkLeafCount' (m : ℕ) :
    Measurable fun ω : ℕ → ℕ => walkLeafCount ω m := by
  have : (fun ω : ℕ → ℕ => walkLeafCount ω m) =
      fun ω => ∑ i ∈ Finset.range m, if (ω i : ℤ) - 1 = -1 then 1 else 0 := by
    funext ω
    unfold walkLeafCount
    rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_from_nat (f := fun a : ℕ => if (a : ℤ) - 1 = -1 then 1 else 0)).comp
      (measurable_pi_apply i)

private theorem walkLeafTime_toNat_eq_iff (ω : ℕ → ℕ) (k m : ℕ) :
    (walkLeafTime ω k).toNat = m ↔
      (walkLeafCount ω m = k ∧ ∀ q, q < m → ¬ walkLeafCount ω q = k) ∨
        (m = 0 ∧ ∀ q, ¬ walkLeafCount ω q = k) := by
  classical
  by_cases hex : ∃ q, walkLeafCount ω q = k
  · have hT : walkLeafTime ω k = (Nat.find hex : ℕ∞) := by
      unfold walkLeafTime
      apply le_antisymm
      · exact iInf₂_le (Nat.find hex) (Nat.find_spec hex)
      · refine le_iInf₂ fun q hq => ?_
        exact_mod_cast Nat.find_min' hex hq
    rw [hT, ENat.toNat_natCast, Nat.find_eq_iff]
    constructor
    · intro h
      exact Or.inl ⟨h.1, fun q hq => h.2 q hq⟩
    · rintro (h | h)
      · exact ⟨h.1, fun q hq => h.2 q hq⟩
      · exact absurd hex (not_exists.2 h.2)
  · have hT : walkLeafTime ω k = ⊤ := by
      unfold walkLeafTime
      simp only [iInf_eq_top]
      intro q hq
      exact absurd ⟨q, hq⟩ hex
    simp only [not_exists] at hex
    rw [hT, ENat.toNat_top]
    constructor
    · rintro rfl
      exact Or.inr ⟨rfl, hex⟩
    · rintro (h | h)
      · exact absurd h.1 (hex m)
      · exact h.1.symm

/-- The walk clock `T_k` (as a natural number, junk `0` at `∞`) is measurable. -/
theorem measurable_walkLeafTime_toNat (k : ℕ) :
    Measurable (fun ω : ℕ → ℕ => (walkLeafTime ω k).toNat) := by
  apply measurable_to_countable'
  intro m
  have hA : ∀ q, MeasurableSet {ω : ℕ → ℕ | walkLeafCount ω q = k} := fun q =>
    measurable_walkLeafCount' q (measurableSet_singleton k)
  have hset : (fun ω : ℕ → ℕ => (walkLeafTime ω k).toNat) ⁻¹' {m} =
      ({ω | walkLeafCount ω m = k} ∩ ⋂ q, ⋂ (_ : q < m), {ω | walkLeafCount ω q = k}ᶜ) ∪
        ({_ω | m = 0} ∩ ⋂ q, {ω | walkLeafCount ω q = k}ᶜ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact walkLeafTime_toNat_eq_iff ω k m
  rw [hset]
  exact ((hA m).inter (MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => (hA q).compl)).union
    ((MeasurableSet.const _).inter (MeasurableSet.iInter fun q => (hA q).compl))

/-- `ω ↦ T_u` is measurable. -/
theorem measurable_leafClock (u : ℝ) : Measurable (fun ω : ℕ → ℕ => leafClock ω u) :=
  measurable_walkLeafTime_toNat ⌊u⌋₊

/-- The real increments are measurable. -/
theorem measurable_walkIncr : Measurable walkIncr := by
  apply Measurable.of_eval
  intro i
  exact (measurable_from_nat (f := fun a : ℕ => (a : ℝ) - 1)).comp (measurable_pi_apply i)

/-! ## Joint time-space scaling (Lemma 5.7) -/

/-- **Joint measurability of the time-space scaling** `(f, k, s) ↦ (t ↦ k f(min(s t, T)))` of
Lemma 5.7 (BGW proves only the fixed-factor case `measurable_timeSpaceScale_fixed`): the Borel
σ-algebra of `D([0,a], E)` is generated by the evaluations (BGW
`measurableSpace_eq_iSup_comap_eval`), and each evaluation is a product of the factor with the
JOINT evaluation `(f, s) ↦ f(s)` (BGW `measurable_eval₂`, right continuity) at a measurable time. -/
theorem measurable_timeSpaceScale {E : Type*} [NormedRing E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {T : ℝ} (a : ℝ) (hT : 0 ≤ T) :
    Measurable (Skorokhod.timeSpaceScale (E := E) a hT) := by
  by_cases ha : 0 ≤ a
  · have heval (t : Set.Icc (0 : ℝ) a) :
        Measurable (fun p : Skorokhod.D T E × E × Set.Ioi (0 : ℝ) =>
          Skorokhod.timeSpaceScale a hT p t) := by
      have hκc : Continuous (fun s : Set.Ioi (0 : ℝ) =>
          (⟨min ((s : ℝ) * t) T, le_min (mul_nonneg (le_of_lt s.2) t.2.1) hT,
            min_le_right _ _⟩ : Set.Icc (0 : ℝ) T)) := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.mul continuous_const).min continuous_const
      have hκ : Measurable (fun p : Skorokhod.D T E × E × Set.Ioi (0 : ℝ) =>
          (⟨min ((p.2.2 : ℝ) * t) T, le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT,
            min_le_right _ _⟩ : Set.Icc (0 : ℝ) T)) :=
        hκc.measurable.comp (measurable_snd.snd)
      have hev : Measurable (fun p : Skorokhod.D T E × E × Set.Ioi (0 : ℝ) =>
          p.1 ⟨min ((p.2.2 : ℝ) * t) T, le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT,
            min_le_right _ _⟩) :=
        Skorokhod.measurable_eval₂.comp (measurable_fst.prodMk hκ)
      exact measurable_snd.fst.mul hev
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (Skorokhod.timeSpaceScale (E := E) a hT)
        (inferInstance : MeasurableSpace (Skorokhod.D a E)) ≤ _
    rw [Skorokhod.measurableSpace_eq_iSup_comap_eval (T := a) (E := E) (S := Set.univ)
      dense_univ ha (by simp)]
    simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
      Function.comp_def]
    intro t _
    exact (heval t).comap_le
  · have hsub : Subsingleton (Skorokhod.D a E) := by
      refine ⟨fun f g => Skorokhod.ext fun t => ?_⟩
      exact absurd (le_trans t.2.1 t.2.2) ha
    exact measurable_of_subsingleton_codomain _

/-- Joint measurability of the time-space scaling of continuous paths (BGW `timeSpaceScaleC`; the
continuous coordinate of the pair form `lem_CVproba_pair` of Lemma 5.7). -/
theorem measurable_timeSpaceScaleC {T : ℝ} (a : ℝ) (hT : 0 ≤ T) :
    Measurable (Skorokhod.timeSpaceScaleC (E := ℝ) a hT) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  have hκc : Continuous (fun s : Set.Ioi (0 : ℝ) =>
      (⟨min ((s : ℝ) * t) T, le_min (mul_nonneg (le_of_lt s.2) t.2.1) hT,
        min_le_right _ _⟩ : Set.Icc (0 : ℝ) T)) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.mul continuous_const).min continuous_const
  have hκ : Measurable (fun p : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ × Set.Ioi (0 : ℝ) =>
      (⟨min ((p.2.2 : ℝ) * t) T, le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT,
        min_le_right _ _⟩ : Set.Icc (0 : ℝ) T)) :=
    hκc.measurable.comp (measurable_snd.snd)
  have heval₂ : Measurable (fun q : Set.Icc (0 : ℝ) T × C(Set.Icc (0 : ℝ) T, ℝ) => q.2 q.1) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (s : Set.Icc (0 : ℝ) T)
      (g : C(Set.Icc (0 : ℝ) T, ℝ)) => g s) (fun g => g.continuous)
      (fun s => (continuous_eval_const s).measurable)
  exact measurable_snd.fst.mul (heval₂.comp (hκ.prodMk measurable_fst))

/-- The path of Lemma 6.2(ii) is a measurable function of the walk. -/
theorem measurable_leafClockPath (μ0 : ℝ) (B : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Measurable (leafClockPath μ0 B n ha) := by
  have hstep : Measurable (fun ω : ℕ → ℕ =>
      Skorokhod.realStepPath 1 (leafClock ω (a * n)) (B ⌊(n : ℝ) / μ0⌋₊) (walkIncr ω)) :=
    measurable_comp_nat (G := fun k ω => Skorokhod.realStepPath 1 k (B ⌊(n : ℝ) / μ0⌋₊)
      (walkIncr ω)) (measurable_leafClock (a * n))
      (fun k => (Skorokhod.measurable_realStepPath 1 k _).comp measurable_walkIncr)
  exact (measurable_timeSpaceScale (E := ℝ) a zero_le_one).comp
    (hstep.prodMk (measurable_const.prodMk measurable_const))

end BGWLeaves
