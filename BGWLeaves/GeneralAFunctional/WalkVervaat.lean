module

public import BGWLeaves.GeneralAFunctional.WalkCyclic
public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.LeafLimits.Helpers

/-! The A-marked discrete Vervaat identity, retaining the random total length. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.WalkVervaat

open MeasureTheory ProbabilityTheory Filter BGW BGW.LocallyFinite
open BGW.StableTrees BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.WalkCyclic
open scoped ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Recode arbitrary offspring marks as zeros, solely to use the existing measurable clock. -/
def markIndicator (A : Set ℕ) (ω : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if ω i ∈ A then 0 else 1

def aMarkTime (A : Set ℕ) (n : ℕ) (ω : ℕ → ℕ) : ℕ :=
  markTime n (markIndicator A ω)

theorem walkLeafCount_markIndicator (A : Set ℕ) (ω : ℕ → ℕ) (k : ℕ) :
    walkLeafCount (markIndicator A ω) k = walkACount A ω k := by
  unfold walkLeafCount walkACount
  congr 1
  ext i
  simp [markIndicator]

theorem measurable_markIndicator (A : Set ℕ) : Measurable (markIndicator A) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_from_top (f := fun a : ℕ => if a ∈ A then 0 else 1)).comp
    (measurable_pi_apply i)

theorem measurable_aMarkTime (A : Set ℕ) (n : ℕ) : Measurable (aMarkTime A n) :=
  (measurable_markTime n).comp (measurable_markIndicator A)

theorem aMarkTime_eq {A : Set ℕ} {n : ℕ} {ω : ℕ → ℕ} {m : ℕ}
    (h : IsAMarkTime A n ω m) : aMarkTime A n ω = m := by
  have he : walkLeafTime (markIndicator A ω) n = (m : ℕ∞) := by
    unfold walkLeafTime
    apply le_antisymm
    · exact iInf₂_le m (by rw [walkLeafCount_markIndicator]; exact h.1)
    · refine le_iInf₂ fun q hq => ?_
      rw [walkLeafCount_markIndicator] at hq
      have hle : m ≤ q := by
        by_contra hlt
        have := h.2 q (not_le.mp hlt)
        omega
      exact_mod_cast hle
  unfold aMarkTime markTime
  rw [he]
  rfl

/-- Rescaled walk at the nth A-mark, with its own random length in the norming. -/
def aBridgeWalkPath (A : Set ℕ) (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ) : Skorokhod.D 1 ℝ :=
  Skorokhod.stepPath (walkWord ω (aMarkTime A n ω)) (B (aMarkTime A n ω))

theorem measurable_aBridgeWalkPath (A : Set ℕ) (B : ℕ → ℝ) (n : ℕ) :
    Measurable (aBridgeWalkPath A B n) :=
  measurable_comp_nat (G := fun k ω => Skorokhod.stepPath (walkWord ω k) (B k))
    (measurable_aMarkTime A n) (fun k => measurable_stepPath_walkWord k (B k))

def treeWord (τ : LocallyFinite.Tree) : List ℤ := (toPlaneTree τ).increments

def walkVWord (A : Set ℕ) (n : ℕ) (ω : ℕ → ℕ) : List ℤ :=
  vervaat (walkWord ω (aMarkTime A n ω))

variable [MeasurableSpace (List ℤ)] [MeasurableSingletonClass (List ℤ)]

omit [MeasurableSingletonClass (List ℤ)] in
theorem measurable_treeWord : Measurable treeWord :=
  measurable_comp_toPlaneTree (fun t => t.increments)

omit [MeasurableSingletonClass (List ℤ)] in
private theorem measurable_vervaat_walkWord (k : ℕ) :
    Measurable (fun ω : ℕ → ℕ => vervaat (walkWord ω k)) := by
  let R : (ℕ → ℕ) → (Fin k → ℕ) := fun ω i => ω i
  have hR : Measurable R := measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  let F : (Fin k → ℕ) → List ℤ := fun x =>
    vervaat (walkWord (fun i => if h : i < k then x ⟨i, h⟩ else 0) k)
  have he : (fun ω : ℕ → ℕ => vervaat (walkWord ω k)) = F ∘ R := by
    funext ω
    dsimp [F, R]
    congr 1
    unfold walkWord
    exact List.map_congr_left fun i hi => by simp [List.mem_range.mp hi]
  rw [he]
  exact (measurable_of_countable F).comp hR

omit [MeasurableSingletonClass (List ℤ)] in
theorem measurable_walkVWord (A : Set ℕ) (n : ℕ) : Measurable (walkVWord A n) :=
  measurable_comp_nat (G := fun k ω => vervaat (walkWord ω k)) (measurable_aMarkTime A n)
    measurable_vervaat_walkWord

/-- H: equality of complete word laws, before projecting away the length. -/
theorem conditional_word_law (μ : PMF ℕ) (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map
        treeWord =
      ((iidWalk μ)[|bridgeAtAMark A n]).map (walkVWord A n) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply measurable_treeWord (measurableSet_singleton x),
    Measure.map_apply (measurable_walkVWord A n) (measurableSet_singleton x)]
  have e1 : ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}])
      (treeWord ⁻¹' {x}) =
      ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}])
        (treeWordAMarks A n x) := by
    rw [cond_apply (measurableSet_zetaAEvent A n), cond_apply (measurableSet_zetaAEvent A n)]
    congr 2
    ext τ
    constructor
    · rintro ⟨⟨hτ, hnτ⟩, hx⟩
      obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).mpr hτ
      refine ⟨⟨t.finiteVertices_toLocallyFinite, hnτ⟩, t, rfl, ?_, ?_⟩
      · simpa [treeWord, toPlaneTree_toLocallyFinite] using hx
      · simpa only [GeneralA.MarkedLaw.zetaA_toLocallyFinite, ENat.natCast_inj] using hnτ
    · rintro ⟨hT, t, rfl, hx, -⟩
      exact ⟨hT, by simp [treeWord, toPlaneTree_toLocallyFinite, hx]⟩
  have e2 : ((iidWalk μ)[|bridgeAtAMark A n]) (walkVWord A n ⁻¹' {x}) =
      ((iidWalk μ)[|bridgeAtAMark A n]) (vervaatAtAMark A n x) := by
    rw [cond_apply (measurableSet_bridgeAtAMark A n), cond_apply (measurableSet_bridgeAtAMark A n)]
    congr 2
    ext ω
    constructor
    · rintro ⟨⟨k, hk, hs⟩, hx⟩
      refine ⟨⟨k, hk, hs⟩, k, hk, hs, ?_⟩
      change walkVWord A n ω = x at hx
      simpa only [walkVWord, aMarkTime_eq hk] using hx
    · rintro ⟨hb, k, hk, hs, hx⟩
      refine ⟨hb, ?_⟩
      change walkVWord A n ω = x
      simpa only [walkVWord, aMarkTime_eq hk] using hx
  rw [e1, e2]
  exact (WalkCyclic.prop_vervaatdiscrete μ A hn x).symm

/-- H in joint word-and-length form. No assumption that the tree's last vertex
is marked occurs: the length is recovered from its complete increment word. -/
theorem conditional_word_length_law (μ : PMF ℕ) (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map
        (fun τ => (treeWord τ, treeSize τ)) =
      ((iidWalk μ)[|bridgeAtAMark A n]).map
        (fun ω => (walkVWord A n ω, aMarkTime A n ω)) := by
  have hT : ∀ᵐ τ ∂((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]),
      (treeWord τ, treeSize τ) = (treeWord τ, (treeWord τ).length) := by
    filter_upwards [ae_cond_mem (measurableSet_zetaAEvent A n)] with τ hτ
    obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).mpr hτ.1
    simp [treeWord, toPlaneTree_toLocallyFinite, treeSize_toLocallyFinite,
      PlaneTree.length_increments]
  have hW : ∀ᵐ ω ∂((iidWalk μ)[|bridgeAtAMark A n]),
      (walkVWord A n ω, aMarkTime A n ω) =
        (walkVWord A n ω, (walkVWord A n ω).length) := by
    exact Filter.Eventually.of_forall fun ω => by simp [walkVWord, length_vervaat, walkWord]
  rw [Measure.map_congr hT, Measure.map_congr hW]
  calc
    _ = (((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map
        treeWord).map (fun x => (x, x.length)) :=
      (Measure.map_map (measurable_of_countable (fun x : List ℤ => (x, x.length)))
        measurable_treeWord).symm
    _ = (((iidWalk μ)[|bridgeAtAMark A n]).map (walkVWord A n)).map
        (fun x => (x, x.length)) := by rw [conditional_word_law μ A hn]
    _ = _ := Measure.map_map (measurable_of_countable (fun x : List ℤ => (x, x.length)))
      (measurable_walkVWord A n)

end

noncomputable section
attribute [local instance] Classical.propDecidable
private local instance wordMeasurableSpace : MeasurableSpace (List ℤ) := ⊤
private local instance wordMeasurableSingletonClass : MeasurableSingletonClass (List ℤ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

private def wordPath (B : ℕ → ℝ) (x : List ℤ) : Skorokhod.D 1 ℝ :=
  Skorokhod.stepPath x (B x.length)

/-- **Corollary 6.7 (`cor:vervaatC`)**, null-safe measure form. -/
theorem cor_vervaatC (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ) (hBpos : ∀ m, 1 ≤ m → 0 < B m) {n : ℕ}
    (hn : 1 ≤ n) :
    ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      ((iidWalk μ)[|bridgeAtAMark A n]).map (fun ω => Skorokhod.vervaatD (aBridgeWalkPath A B n ω)) := by
  -- the tree path is the word path of the increment word on `{λ = n}`
  have hT : ∀ᵐ τ ∂((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]),
      rescaledLuka (treeSize τ) (B (treeSize τ)) τ = wordPath B (treeWord τ) := by
    filter_upwards [ae_cond_mem (measurableSet_zetaAEvent A n)] with τ hτ
    obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).mpr hτ.1
    rw [rescaledLuka_eq_stepPath _ t.finiteVertices_toLocallyFinite]
    unfold wordPath treeWord
    rw [toPlaneTree_toLocallyFinite, treeIncrements_toLocallyFinite, treeSize_toLocallyFinite,
      PlaneTree.length_increments]
  -- the Vervaat transform of the walk path is the word path of the Vervaat word on `{W_{T_n} = -1}`
  have hW : ∀ᵐ ω ∂((iidWalk μ)[|bridgeAtAMark A n]),
      Skorokhod.vervaatD (aBridgeWalkPath A B n ω) = wordPath B (walkVWord A n ω) := by
    filter_upwards [ae_cond_mem (measurableSet_bridgeAtAMark A n)] with ω hω
    obtain ⟨k, hk, hs⟩ := hω
    have hmk := aMarkTime_eq hk
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp [walkSum] at hs
      · exact h
    have hlen : (walkWord ω k).length = k := by simp [walkWord]
    have hneg : ∃ j, 1 ≤ j ∧ j ≤ (walkWord ω k).length ∧ ((walkWord ω k).take j).sum < 0 :=
      ⟨k, hk1, hlen.ge, by rw [List.take_of_length_le hlen.le, sum_walkWord, hs]; norm_num⟩
    unfold aBridgeWalkPath walkVWord wordPath
    rw [hmk, LeafLimits.Helpers.vervaatD_stepPath_vervaat hneg (hBpos k hk1), length_vervaat, hlen]
  have hwords := conditional_word_law μ A hn
  calc ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ)
      = ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map (wordPath B ∘ treeWord) :=
        Measure.map_congr hT
    _ = (((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]).map treeWord).map (wordPath B) :=
        (Measure.map_map measurable_from_top measurable_treeWord).symm
    _ = (((iidWalk μ)[|bridgeAtAMark A n]).map (walkVWord A n)).map (wordPath B) := by rw [hwords]
    _ = ((iidWalk μ)[|bridgeAtAMark A n]).map (wordPath B ∘ walkVWord A n) :=
        Measure.map_map measurable_from_top (measurable_walkVWord A n)
    _ = ((iidWalk μ)[|bridgeAtAMark A n]).map
        (fun ω => Skorokhod.vervaatD (aBridgeWalkPath A B n ω)) :=
        (Measure.map_congr hW).symm

end
end BGWLeaves.GeneralAFunctional.WalkVervaat
