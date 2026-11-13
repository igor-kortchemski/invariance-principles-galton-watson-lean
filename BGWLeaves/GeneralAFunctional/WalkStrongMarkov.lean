module

public import BGWLeaves.GeneralAFunctional.Walk
public import BGWLeaves.Conditioning.Defs
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-! Strong Markov and the exact stopped-prefix density for arbitrary offspring marks.
The original offspring sequence and its walk are retained throughout. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkStrongMarkov
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open scoped ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

def timeE (A : Set ℕ) (ω : ℕ → ℕ) (n : ℕ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : walkACount A ω k = n), (k : ℕ∞)

def stopPos (A : Set ℕ) (ω : ℕ → ℕ) (n : ℕ) : ℤ := walkSum ω (timeE A ω n).toNat

def stopPath (A : Set ℕ) (ω : ℕ → ℕ) (n : ℕ) : List ℤ :=
  (List.range ((timeE A ω n).toNat + 1)).map (walkSum ω)

def stopEvent (A : Set ℕ) (n : ℕ) (x : ℤ) : Set (ℕ → ℕ) :=
  {ω | timeE A ω n ≠ ⊤ ∧ stopPos A ω n = x}

private theorem exists_mark_iff (A : Set ℕ) (n : ℕ) (ω : ℕ → ℕ) :
    (∃ m, IsAMarkTime A n ω m) ↔ ∃ m, walkACount A ω m = n := by
  simpa only [WalkClock.isMarkTime_indicator_iff, walkLeafCount_markIndicator] using
    Vervaat.MarkTime.exists_isMarkTime_iff n (markIndicator A ω)

/-! ## Deterministic bookkeeping -/

private theorem wlc_succ (A : Set ℕ) (ω : ℕ → ℕ) (n : ℕ) :
    walkACount A ω (n + 1) = walkACount A ω n + if ω n ∈ A then 1 else 0 := by
  unfold walkACount 
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]

private theorem wlc_zero (A : Set ℕ) (ω : ℕ → ℕ) : walkACount A ω 0 = 0 := by
  simp [walkACount]

private theorem wlc_add (A : Set ℕ) (ω : ℕ → ℕ) (t s : ℕ) :
    walkACount A ω (t + s) = walkACount A ω t + walkACount A (shiftSeq t ω) s := by
  induction s with
  | zero => simp [wlc_zero A]
  | succ s ih =>
    rw [← add_assoc, wlc_succ A, ih, wlc_succ A]
    by_cases h : ω (t + s) ∈ A <;> simp [shiftSeq, h, add_assoc]

private theorem walkSum_add' (ω : ℕ → ℕ) (t s : ℕ) :
    walkSum ω (t + s) = walkSum ω t + walkSum (shiftSeq t ω) s := by
  unfold walkSum
  rw [Finset.sum_range_add]
  rfl

private theorem wlc_congr (A : Set ℕ) {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    walkACount A ω q = walkACount A ω' q := by
  induction q with
  | zero => simp [wlc_zero A]
  | succ q ih =>
    rw [wlc_succ A, wlc_succ A, ih (fun i hi => h i (by omega)), h q (by omega)]

private theorem walkSum_congr {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    walkSum ω q = walkSum ω' q := by
  unfold walkSum
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

private theorem isMarkTime_unique (A : Set ℕ) {n : ℕ} {ω : ℕ → ℕ} {k k' : ℕ} (h : IsAMarkTime A n ω k)
    (h' : IsAMarkTime A n ω k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := h'.2 k hlt
    have h2 := h.1
    omega
  · have h1 := h.2 k' hlt
    have h2 := h'.1
    omega

private theorem isMarkTime_walkLeafTime (A : Set ℕ) {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} (h : IsAMarkTime A n ω m) :
    timeE A ω n = (m : ℕ∞) := by
  unfold timeE 
  apply le_antisymm
  · exact iInf₂_le m h.1
  · refine le_iInf₂ fun q hq => ?_
    have : m ≤ q := by
      by_contra hlt
      have := h.2 q (not_le.1 hlt)
      omega
    exact_mod_cast this

private theorem walkLeafTime_ne_top_iff (A : Set ℕ) {n : ℕ} {ω : ℕ → ℕ} :
    timeE A ω n ≠ ⊤ ↔ ∃ m, IsAMarkTime A n ω m := by
  constructor
  · intro h
    by_contra hne
    apply h
    have : ¬ ∃ m, walkACount A ω m = n := by
      rw [← exists_mark_iff A]; exact hne
    unfold timeE 
    simp only [iInf_eq_top]
    intro m hm
    exact absurd ⟨m, hm⟩ this
  · rintro ⟨m, hm⟩
    rw [isMarkTime_walkLeafTime A hm]
    exact ENat.natCast_ne_top m

private theorem walkLeafTime_eq_coe_iff (A : Set ℕ) {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} :
    timeE A ω n = (m : ℕ∞) ↔ IsAMarkTime A n ω m := by
  constructor
  · intro h
    have hne : timeE A ω n ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top m
    obtain ⟨m', hm'⟩ := (walkLeafTime_ne_top_iff A).1 hne
    have := isMarkTime_walkLeafTime A hm'
    rw [h] at this
    have : m = m' := by exact_mod_cast this
    subst this
    exact hm'
  · exact isMarkTime_walkLeafTime A

theorem walkLeafTime_ne_top_ae (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) :
    ∀ᵐ ω ∂iidWalk μ, ∀ k : ℕ, timeE A ω k ≠ ⊤ := by
  filter_upwards [WalkClock.ae_exists_aMarkTime μ A h0] with ω hω k
  exact (walkLeafTime_ne_top_iff A).2 (hω k)

theorem walkLeafTime_add (A : Set ℕ) (ω : ℕ → ℕ) {k n : ℕ} (hkn : k ≤ n) (hk : timeE A ω k ≠ ⊤) :
    timeE A ω n = timeE A ω k + timeE A (shiftSeq (timeE A ω k).toNat ω) (n - k) ∧
      (timeE A ω n ≠ ⊤ →
        stopPos A ω n = stopPos A ω k +
          stopPos A (shiftSeq (timeE A ω k).toNat ω) (n - k)) := by
  obtain ⟨t, ht⟩ := (walkLeafTime_ne_top_iff A).1 hk
  have hTk : timeE A ω k = (t : ℕ∞) := isMarkTime_walkLeafTime A ht
  rw [hTk]
  simp only [ENat.toNat_natCast]
  by_cases hex : ∃ s, IsAMarkTime A (n - k) (shiftSeq t ω) s
  · obtain ⟨s, hs⟩ := hex
    have hn : IsAMarkTime A n ω (t + s) := by
      refine ⟨by rw [wlc_add A, ht.1, hs.1]; omega, fun q hq => ?_⟩
      by_cases hqt : q < t
      · have := ht.2 q hqt
        omega
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hqt)
        have hr : r < s := by omega
        have := hs.2 r hr
        rw [wlc_add A, ht.1]
        omega
    rw [isMarkTime_walkLeafTime A hn, isMarkTime_walkLeafTime A hs]
    refine ⟨by push_cast; rfl, fun _ => ?_⟩
    unfold stopPos 
    rw [isMarkTime_walkLeafTime A hn, isMarkTime_walkLeafTime A hs, isMarkTime_walkLeafTime A ht]
    simp only [ENat.toNat_natCast]
    exact walkSum_add' ω t s
  · have htop : timeE A (shiftSeq t ω) (n - k) = ⊤ := by
      by_contra h
      exact hex ((walkLeafTime_ne_top_iff A).1 h)
    have htopn : timeE A ω n = ⊤ := by
      by_contra h
      obtain ⟨m, hm⟩ := (walkLeafTime_ne_top_iff A).1 h
      apply hex
      have hmt : t ≤ m := by
        by_contra hlt
        have := ht.2 m (not_le.1 hlt)
        have := hm.1
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hmt
      have : walkACount A (shiftSeq t ω) s = n - k := by
        have h1 := hm.1
        rw [wlc_add A, ht.1] at h1
        omega
      exact (exists_mark_iff A _ _).2 ⟨s, this⟩
    rw [htop, htopn]
    exact ⟨by simp, fun h => absurd rfl h⟩

/-! ## Prefix / tail decomposition -/

/-- The first `m` coordinates. -/
private def pref (m : ℕ) (ω : ℕ → ℕ) : Fin m → ℕ := fun i => ω i

/-- Extension of a finite prefix by zeros. -/
private def extendZ (m : ℕ) (x : Fin m → ℕ) : ℕ → ℕ := fun i => if h : i < m then x ⟨i, h⟩ else 0

private theorem measurable_pref (m : ℕ) : Measurable (pref m) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

private theorem measurable_shiftSeq (m : ℕ) : Measurable (shiftSeq m) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

private theorem extendZ_pref_agree (m : ℕ) (ω : ℕ → ℕ) : ∀ i < m, ω i = extendZ m (pref m ω) i := by
  intro i hi
  simp [extendZ, pref, hi]

private theorem measurableSet_of_dependsOn {m : ℕ} {S : Set (ℕ → ℕ)}
    (h : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S)) : MeasurableSet S := by
  have : S = pref m ⁻¹' {y | extendZ m y ∈ S} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact h _ _ (extendZ_pref_agree m ω)
  rw [this]
  exact measurable_pref m (Set.to_countable _).measurableSet

private theorem indep_pref_shift (μ : PMF ℕ) (m : ℕ) :
    IndepFun (pref m) (shiftSeq m) (iidWalk μ) := by
  have hI : iIndepFun (fun (i : ℕ) (ω : ℕ → ℕ) => ω i) (iidWalk μ) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ.toMeasure) (X := fun _ x => x) (fun _ => measurable_id)
  have h := hI.indepFun_set (Set.Iio m) (Set.Ici m)
    (Set.disjoint_left.2 fun x hx hx' => by simp only [Set.mem_Iio, Set.mem_Ici] at hx hx'; omega) (fun i => measurable_pi_apply i)
  have h2 := h.comp (φ := fun (s : Set.Iio m → ℕ) (i : Fin m) => s ⟨i, i.2⟩)
    (ψ := fun (s : Set.Ici m → ℕ) (i : ℕ) => s ⟨m + i, by simp⟩)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  exact h2

private theorem map_shift (μ : PMF ℕ) (m : ℕ) : (iidWalk μ).map (shiftSeq m) = iidWalk μ := by
  have := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ.toMeasure)
    (f := fun i : ℕ => m + i) (add_right_injective m)
  exact this

private theorem lintegral_shift (μ : PMF ℕ) (m : ℕ) {G : (ℕ → ℕ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, G (shiftSeq m ω) ∂iidWalk μ = ∫⁻ ω, G ω ∂iidWalk μ := by
  rw [← lintegral_map hG (measurable_shiftSeq m), map_shift]

private theorem lintegral_pref_shift (μ : PMF ℕ) (m : ℕ) (A : (Fin m → ℕ) → ℝ≥0∞)
    {G : (ℕ → ℕ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, A (pref m ω) * G (shiftSeq m ω) ∂iidWalk μ =
      (∫⁻ ω, A (pref m ω) ∂iidWalk μ) * ∫⁻ ω, G ω ∂iidWalk μ := by
  have hA : Measurable A := measurable_of_countable A
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (f := fun ω => A (pref m ω)) (g := fun ω => G (shiftSeq m ω))
    (hA.comp (measurable_pref m)) (hG.comp (measurable_shiftSeq m))
    ((indep_pref_shift μ m).comp hA hG)
  rw [← lintegral_shift μ m hG]
  exact this

/-! ## The stopped path and the first-passage pieces -/

private def pathAt (ω : ℕ → ℕ) (m : ℕ) : List ℤ := (List.range (m + 1)).map (walkSum ω)

open scoped Classical in
private noncomputable def Phi (A : Set ℕ) (k : ℕ) (F : List ℤ → ℝ≥0∞) (m : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ :=
  if IsAMarkTime A k ω m then F (pathAt ω m) else 0

private theorem isMarkTime_congr (A : Set ℕ) {k m : ℕ} {ω ω' : ℕ → ℕ} (h : ∀ i < m, ω i = ω' i) :
    IsAMarkTime A k ω m ↔ IsAMarkTime A k ω' m := by
  unfold IsAMarkTime 
  rw [wlc_congr A h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => by rw [← wlc_congr A (fun i hi => h i (by omega))]; exact h2 q hq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => by rw [wlc_congr A (fun i hi => h i (by omega))]; exact h2 q hq⟩

private theorem pathAt_congr {m : ℕ} {ω ω' : ℕ → ℕ} (h : ∀ i < m, ω i = ω' i) :
    pathAt ω m = pathAt ω' m := by
  unfold pathAt
  refine List.map_congr_left fun q hq => ?_
  have : q < m + 1 := List.mem_range.1 hq
  exact walkSum_congr fun i hi => h i (by omega)

private theorem Phi_congr (A : Set ℕ) (k : ℕ) (F : List ℤ → ℝ≥0∞) (m : ℕ) {ω ω' : ℕ → ℕ}
    (h : ∀ i < m, ω i = ω' i) : Phi A k F m ω = Phi A k F m ω' := by
  unfold Phi 
  have := isMarkTime_congr A (k := k) h
  by_cases hm : IsAMarkTime A k ω m
  · have hm' := this.1 hm
    simp [hm, hm', pathAt_congr h]
  · have hm' : ¬ IsAMarkTime A k ω' m := fun h' => hm (this.2 h')
    simp [hm, hm']

private theorem Phi_eq_comp (A : Set ℕ) (k : ℕ) (F : List ℤ → ℝ≥0∞) (m : ℕ) :
    Phi A k F m = fun ω => Phi A k F m (extendZ m (pref m ω)) :=
  funext fun ω => Phi_congr A k F m (extendZ_pref_agree m ω)

private theorem measurable_Phi (A : Set ℕ) (k : ℕ) (F : List ℤ → ℝ≥0∞) (m : ℕ) : Measurable (Phi A k F m) := by
  rw [Phi_eq_comp A]
  exact (measurable_of_countable fun y : Fin m → ℕ => Phi A k F m (extendZ m y)).comp (measurable_pref m)

/-- Pointwise decomposition on `{T_k < ∞}`. -/
private theorem decomp_ae (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) (k : ℕ) (F : List ℤ → ℝ≥0∞)
    (G : (ℕ → ℕ) → ℝ≥0∞) :
    ∀ᵐ ω ∂iidWalk μ, F (stopPath A ω k) * G (shiftSeq (timeE A ω k).toNat ω) =
      ∑' m, Phi A k F m ω * G (shiftSeq m ω) := by
  filter_upwards [walkLeafTime_ne_top_ae A h0] with ω hω
  obtain ⟨m0, hm0⟩ := (walkLeafTime_ne_top_iff A).1 (hω k)
  have hT := isMarkTime_walkLeafTime A hm0
  rw [tsum_eq_single m0]
  · simp [Phi, hm0, hT, stopPath, pathAt]
  · intro m hm
    have : ¬ IsAMarkTime A k ω m := fun h => hm (isMarkTime_unique A h hm0)
    simp [Phi, this]

private theorem aemeasurable_stop (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) (k : ℕ) (F : List ℤ → ℝ≥0∞)
    {G : (ℕ → ℕ) → ℝ≥0∞} (hG : Measurable G) :
    AEMeasurable (fun ω => F (stopPath A ω k) * G (shiftSeq (timeE A ω k).toNat ω))
      (iidWalk μ) := by
  refine AEMeasurable.congr ?_ ((decomp_ae A h0 k F G).mono fun ω h => h.symm)
  exact (Measurable.tsum fun m =>
    (measurable_Phi A k F m).mul (hG.comp (measurable_shiftSeq m))).aemeasurable

/-- **Strong Markov property of the walk at the `k`-th leaf time.** -/
theorem strongMarkov_leafTime (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) (k : ℕ) (F : List ℤ → ℝ≥0∞)
    (G : (ℕ → ℕ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ω, F (stopPath A ω k) * G (shiftSeq (timeE A ω k).toNat ω) ∂iidWalk μ =
      (∫⁻ ω, F (stopPath A ω k) ∂iidWalk μ) * ∫⁻ ω, G ω ∂iidWalk μ := by
  have hdec : ∀ G' : (ℕ → ℕ) → ℝ≥0∞, Measurable G' →
      ∫⁻ ω, F (stopPath A ω k) * G' (shiftSeq (timeE A ω k).toNat ω) ∂iidWalk μ =
        ∑' m, (∫⁻ ω, Phi A k F m ω ∂iidWalk μ) * ∫⁻ ω, G' ω ∂iidWalk μ := by
    intro G' hG'
    rw [lintegral_congr_ae (decomp_ae A h0 k F G')]
    refine (lintegral_tsum fun m =>
        ((measurable_Phi A k F m).mul (hG'.comp (measurable_shiftSeq m))).aemeasurable).trans ?_
    refine tsum_congr fun m => ?_
    have hA : Phi A k F m = fun ω => (fun y => Phi A k F m (extendZ m y)) (pref m ω) := Phi_eq_comp A k F m
    rw [hA]
    exact lintegral_pref_shift μ m _ hG'
  have h1 := hdec G hG
  have h2 := hdec (fun _ => 1) measurable_const
  simp only [mul_one, lintegral_const, measure_univ] at h2
  rw [h1, h2, ENNReal.tsum_mul_right]

/-! ## The unconditioned form of Lemma 6.10 -/

private noncomputable def lastPos (p : List ℤ) : ℤ := p.getLastD 0

private theorem lastPos_walkStopPath (A : Set ℕ) (ω : ℕ → ℕ) (k : ℕ) :
    lastPos (stopPath A ω k) = stopPos A ω k := by
  unfold lastPos stopPath  stopPos 
  generalize (timeE A ω k).toNat = N
  rw [List.range_succ, List.map_append]
  simp [List.getLastD_eq_getLast?]

private theorem walkStopEvent_eq_iUnion (A : Set ℕ) (j : ℕ) (x : ℤ) :
    stopEvent A j x = ⋃ m : ℕ, {ω | IsAMarkTime A j ω m ∧ walkSum ω m = x} := by
  ext ω
  simp only [stopEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hne, hx⟩
    obtain ⟨m, hm⟩ := (walkLeafTime_ne_top_iff A).1 hne
    refine ⟨m, hm, ?_⟩
    rw [← hx]
    unfold stopPos 
    rw [isMarkTime_walkLeafTime A hm, ENat.toNat_natCast]
  · rintro ⟨m, hm, hx⟩
    refine ⟨(walkLeafTime_ne_top_iff A).2 ⟨m, hm⟩, ?_⟩
    unfold stopPos 
    rw [isMarkTime_walkLeafTime A hm, ENat.toNat_natCast, hx]

theorem stopEvent_eq (A : Set ℕ) (n : ℕ) (z : ℤ) :
    stopEvent A n z = WalkStopped.aStopEvent A n z := by
  rw [walkStopEvent_eq_iUnion]
  ext ω
  simp [WalkStopped.aStopEvent]

theorem chiA_eq_stopEvent (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) (j : ℤ) :
    WalkLocal.chiA μ A n j = iidWalk μ (stopEvent A n (-1-j)) := by
  rw [stopEvent_eq]
  rfl

private theorem measurableSet_walkStopEvent (A : Set ℕ) (j : ℕ) (x : ℤ) : MeasurableSet (stopEvent A j x) := by
  rw [walkStopEvent_eq_iUnion A]
  refine MeasurableSet.iUnion fun m => measurableSet_of_dependsOn (m := m) ?_
  intro ω ω' h
  simp only [Set.mem_ofPred_eq]
  rw [isMarkTime_congr A h, walkSum_congr h]

private theorem aemeasurable_path (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) (k : ℕ) (F : List ℤ → ℝ≥0∞) :
    AEMeasurable (fun ω => F (stopPath A ω k)) (iidWalk μ) := by
  simpa using aemeasurable_stop A h0 k F (G := fun _ => 1) measurable_const

theorem absolueC2_core (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) {n k : ℕ} (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω in stopEvent A n (-1), f (stopPath A ω k) ∂iidWalk μ =
      ∫⁻ ω, f (stopPath A ω k) * WalkLocal.chiA μ A (n - k) (stopPos A ω k) ∂iidWalk μ := by
  classical
  let Fx : ℤ → List ℤ → ℝ≥0∞ := fun x p => f p * (if lastPos p = x then 1 else 0)
  let Gx : ℤ → (ℕ → ℕ) → ℝ≥0∞ := fun x =>
    (stopEvent A (n - k) (-1 - x)).indicator (fun _ => 1)
  have hGx : ∀ x, Measurable (Gx x) := fun x =>
    measurable_const.indicator (measurableSet_walkStopEvent A _ _)
  have hGint : ∀ x, ∫⁻ ω, Gx x ω ∂iidWalk μ = WalkLocal.chiA μ A (n - k) x := by
    intro x
    simp only [Gx]
    rw [lintegral_indicator_const (measurableSet_walkStopEvent A _ _), one_mul]
    exact (chiA_eq_stopEvent μ A _ _).symm
  have hFint : ∀ x, ∫⁻ ω, Fx x (stopPath A ω k) ∂iidWalk μ =
      ∫⁻ ω, f (stopPath A ω k) * (if stopPos A ω k = x then 1 else 0) ∂iidWalk μ := by
    intro x
    simp only [Fx, lastPos_walkStopPath A]
  have hL : ∀ᵐ ω ∂iidWalk μ,
      (stopEvent A n (-1)).indicator (fun ω => f (stopPath A ω k)) ω =
        ∑' x, Fx x (stopPath A ω k) * Gx x (shiftSeq (timeE A ω k).toNat ω) := by
    filter_upwards [walkLeafTime_ne_top_ae A h0] with ω hω
    have hk := hω k
    obtain ⟨hadd1, hadd2⟩ := walkLeafTime_add A ω hkn.le hk
    set ω' := shiftSeq (timeE A ω k).toNat ω with hω'
    rw [tsum_eq_single (stopPos A ω k)]
    · have hmem : ω ∈ stopEvent A n (-1) ↔ ω' ∈ stopEvent A (n - k) (-1 - stopPos A ω k) := by
        simp only [stopEvent, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hne, hx⟩
          have hne' : timeE A ω' (n - k) ≠ ⊤ := by
            intro htop
            apply hne
            rw [hadd1, htop]
            exact add_top _
          refine ⟨hne', ?_⟩
          have := hadd2 hne
          omega
        · rintro ⟨hne', hx⟩
          have hne : timeE A ω n ≠ ⊤ := by
            rw [hadd1]
            exact WithTop.add_ne_top.2 ⟨hk, hne'⟩
          refine ⟨hne, ?_⟩
          have := hadd2 hne
          omega
      by_cases hS : ω ∈ stopEvent A n (-1)
      · have hS' := hmem.1 hS
        simp [Fx, Gx, hS, hS', lastPos_walkStopPath A]
      · have hS' : ω' ∉ stopEvent A (n - k) (-1 - stopPos A ω k) := fun h => hS (hmem.2 h)
        simp [Fx, Gx, hS, hS', lastPos_walkStopPath A]
    · intro x hx
      simp [Fx, lastPos_walkStopPath A, Ne.symm hx]
  rw [← lintegral_indicator (measurableSet_walkStopEvent A n (-1)), lintegral_congr_ae hL]
  rw [lintegral_tsum fun x =>
    (aemeasurable_stop A h0 k (Fx x) (hGx x))]
  have hR : ∀ ω : ℕ → ℕ, f (stopPath A ω k) * WalkLocal.chiA μ A (n - k) (stopPos A ω k) =
      ∑' x, Fx x (stopPath A ω k) * WalkLocal.chiA μ A (n - k) x := by
    intro ω
    rw [tsum_eq_single (stopPos A ω k)]
    · simp [Fx, lastPos_walkStopPath A]
    · intro x hx
      simp [Fx, lastPos_walkStopPath A, Ne.symm hx]
  simp_rw [hR]
  rw [lintegral_tsum fun x => (aemeasurable_path A h0 k (Fx x)).mul_const _]
  refine tsum_congr fun x => ?_
  rw [strongMarkov_leafTime A h0 k (Fx x) (Gx x) (hGx x), hGint,
    lintegral_mul_const' _ _ (show WalkLocal.chiA μ A (n-k) x ≠ ⊤ from measure_ne_top _ _)]

theorem lem_absolueC2_k (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0) {n k : ℕ} (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω, f (stopPath A ω k) ∂((iidWalk μ)[|stopEvent A n (-1)]) =
      ∫⁻ ω, f (stopPath A ω k) * (WalkLocal.chiA μ A (n - k) (stopPos A ω k) / WalkLocal.chiA μ A n 0) ∂iidWalk μ := by
  have hchi0 : WalkLocal.chiA μ A n 0 = iidWalk μ (stopEvent A n (-1)) := by simpa using chiA_eq_stopEvent μ A n 0
  have hcore := absolueC2_core A h0 hkn f
  by_cases hz : WalkLocal.chiA μ A n 0 = 0
  · have hz' : iidWalk μ (stopEvent A n (-1)) = 0 := by rw [← hchi0]; exact hz
    rw [cond_eq_zero_of_meas_eq_zero hz', lintegral_zero_measure]
    have h1 := absolueC2_core A h0 hkn (fun _ => 1)
    simp only [Measure.restrict_apply_univ, one_mul, lintegral_const] at h1
    have hae : ∀ᵐ ω ∂iidWalk μ, WalkLocal.chiA μ A (n - k) (stopPos A ω k) = 0 := by
      have hmeas : AEMeasurable (fun ω => WalkLocal.chiA μ A (n - k) (stopPos A ω k)) (iidWalk μ) := by
        simpa only [lastPos_walkStopPath A] using
          aemeasurable_path A h0 k (fun p => WalkLocal.chiA μ A (n - k) (lastPos p))
      refine (lintegral_eq_zero_iff' hmeas).1 ?_
      rw [← h1]
      simpa using hz'
    symm
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · filter_upwards [hae] with ω hω
      simp [hω]
  · have hinv : (WalkLocal.chiA μ A n 0)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hz
    rw [ProbabilityTheory.cond, lintegral_smul_measure, ← hchi0, smul_eq_mul, hcore]
    simp_rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm (f _) ((WalkLocal.chiA μ A n 0)⁻¹), mul_assoc]
    rw [lintegral_const_mul' _ _ hinv]

end
end BGWLeaves.GeneralAFunctional.WalkStrongMarkov
