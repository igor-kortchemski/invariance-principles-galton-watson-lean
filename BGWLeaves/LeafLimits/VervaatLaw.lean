module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Vervaat
import BGWLeaves.LeafLimits.Helpers
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# M13 provider `VervaatLaw`

Provider for Corollary 6.7: the registered hole `cor_vervaatC` of `BGWLeaves.LeafLimits`, exported in
namespace `BGWLeaves.LeafLimits.VervaatLaw` with exactly the type of the statements file.

Route.  Both sides factor through a word: on `{λ = n}` the tree path is `x ↦ stepPath x (B |x|)` at the
increment word `x` of the tree (`rescaledLuka_eq_stepPath`), and on `{W_{T_n} = -1}` the Vervaat
transform of the walk path is the same map at the Vervaat transform of the walk word
(`vervaatD_stepPath_vervaat`, provider `Helpers`; `|V(x)| = |x| = T_n`).  The two laws of the words,
on the countable space `List ℤ` with its discrete σ-algebra (a `local` instance), agree on atoms: this
is Proposition 6.5 (`prop_vervaatdiscrete`, tranche 1), after intersecting the atoms with the
conditioning events.  No positivity of `P_μ[λ = n]` is needed (both conditional measures are `0`
together).
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.VervaatLaw

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- The discrete σ-algebra on words (local: `List ℤ` has no global measurable structure). -/
private local instance wordMeasurableSpace : MeasurableSpace (List ℤ) := ⊤

private local instance wordMeasurableSingletonClass : MeasurableSingletonClass (List ℤ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- `x ↦ (W_{⌊|x| t⌋}(x) / B_{|x|})_{0 ≤ t ≤ 1}`. -/
private noncomputable def wordPath (B : ℕ → ℝ) (x : List ℤ) : Skorokhod.D 1 ℝ :=
  Skorokhod.stepPath x (B x.length)

/-- The increment word of the tree (junk for an infinite tree). -/
private noncomputable def treeWord (τ : LocallyFinite.Tree) : List ℤ := (toPlaneTree τ).increments

/-- The Vervaat transform of the walk word up to `T_n`. -/
private noncomputable def walkVWord (n : ℕ) (ω : ℕ → ℕ) : List ℤ :=
  vervaat (walkWord ω (markTime n ω))

private theorem measurable_treeWord : Measurable treeWord :=
  measurable_comp_toPlaneTree (fun t => t.increments)

private theorem measurable_vervaat_walkWord (k : ℕ) :
    Measurable (fun ω : ℕ → ℕ => vervaat (walkWord ω k)) := by
  let R : (ℕ → ℕ) → (Fin k → ℕ) := fun ω i => ω i
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (i : ℕ)
  let F : (Fin k → ℕ) → List ℤ := fun x =>
    vervaat (walkWord (fun i => if h : i < k then x ⟨i, h⟩ else 0) k)
  have hFR : (fun ω : ℕ → ℕ => vervaat (walkWord ω k)) = F ∘ R := by
    funext ω
    simp only [Function.comp_apply, F, R]
    congr 1
    unfold walkWord
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp [hi]
  rw [hFR]
  exact (measurable_of_countable F).comp hR

private theorem measurable_walkVWord (n : ℕ) : Measurable (walkVWord n) :=
  measurable_comp_nat (G := fun k ω => vervaat (walkWord ω k)) (measurable_markTime n)
    measurable_vervaat_walkWord

private theorem walkLeafTime_eq {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} (h : IsMarkTime n ω m) :
    walkLeafTime ω n = (m : ℕ∞) := by
  unfold walkLeafTime
  apply le_antisymm
  · exact iInf₂_le m h.1
  · refine le_iInf₂ fun q hq => ?_
    have : m ≤ q := by
      by_contra hlt
      have := h.2 q (not_le.1 hlt)
      omega
    exact_mod_cast this

private theorem markTime_eq {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} (h : IsMarkTime n ω m) :
    markTime n ω = m := by
  unfold markTime
  rw [walkLeafTime_eq h]
  rfl

/-- **Corollary 6.7 (`cor:vervaatC`)**, null-safe measure form. -/
theorem cor_vervaatC (μ : PMF ℕ) (B : ℕ → ℝ) (hBpos : ∀ m, 1 ≤ m → 0 < B m) {n : ℕ}
    (hn : 1 ≤ n) :
    ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      ((iidWalk μ)[|bridgeAtMark n]).map (fun ω => Skorokhod.vervaatD (bridgeWalkPath B n ω)) := by
  -- the tree path is the word path of the increment word on `{λ = n}`
  have hT : ∀ᵐ τ ∂((bienaymeLaw μ.toMeasure)[|leafCountEvent n]),
      rescaledLuka (treeSize τ) (B (treeSize τ)) τ = wordPath B (treeWord τ) := by
    filter_upwards [ae_cond_mem (measurableSet_leafCountEvent n)] with τ hτ
    obtain ⟨t, rfl, -⟩ := hτ
    rw [rescaledLuka_eq_stepPath _ t.finiteVertices_toLocallyFinite]
    unfold wordPath treeWord
    rw [toPlaneTree_toLocallyFinite, treeIncrements_toLocallyFinite, treeSize_toLocallyFinite,
      PlaneTree.length_increments]
  -- the Vervaat transform of the walk path is the word path of the Vervaat word on `{W_{T_n} = -1}`
  have hW : ∀ᵐ ω ∂((iidWalk μ)[|bridgeAtMark n]),
      Skorokhod.vervaatD (bridgeWalkPath B n ω) = wordPath B (walkVWord n ω) := by
    filter_upwards [ae_cond_mem (measurableSet_bridgeAtMark n)] with ω hω
    obtain ⟨k, hk, hs⟩ := hω
    have hmk := markTime_eq hk
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp [walkSum] at hs
      · exact h
    have hlen : (walkWord ω k).length = k := by simp [walkWord]
    have hneg : ∃ j, 1 ≤ j ∧ j ≤ (walkWord ω k).length ∧ ((walkWord ω k).take j).sum < 0 :=
      ⟨k, hk1, hlen.ge, by rw [List.take_of_length_le hlen.le, sum_walkWord, hs]; norm_num⟩
    unfold bridgeWalkPath walkVWord wordPath
    rw [hmk, Helpers.vervaatD_stepPath_vervaat hneg (hBpos k hk1), length_vervaat, hlen]
  -- the laws of the two words agree (Proposition 6.5)
  have hwords : ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).map treeWord =
      ((iidWalk μ)[|bridgeAtMark n]).map (walkVWord n) := by
    apply Measure.ext_of_singleton
    intro x
    rw [Measure.map_apply measurable_treeWord (measurableSet_singleton x),
      Measure.map_apply (measurable_walkVWord n) (measurableSet_singleton x)]
    have e1 : ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) (treeWord ⁻¹' {x}) =
        ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) (treeWordLeaves n x) := by
      rw [cond_apply (measurableSet_leafCountEvent n), cond_apply (measurableSet_leafCountEvent n)]
      congr 2
      ext τ
      constructor
      · rintro ⟨⟨t, rfl, hdeg⟩, hx⟩
        refine ⟨⟨t, rfl, hdeg⟩, t, rfl, ?_, hdeg⟩
        simpa [treeWord, toPlaneTree_toLocallyFinite] using hx
      · rintro ⟨hL, t, rfl, hx, -⟩
        refine ⟨hL, ?_⟩
        simp [treeWord, toPlaneTree_toLocallyFinite, hx]
    have e2 : ((iidWalk μ)[|bridgeAtMark n]) (walkVWord n ⁻¹' {x}) =
        ((iidWalk μ)[|bridgeAtMark n]) (vervaatAtMark n x) := by
      rw [cond_apply (measurableSet_bridgeAtMark n), cond_apply (measurableSet_bridgeAtMark n)]
      congr 2
      ext ω
      constructor
      · rintro ⟨⟨k, hk, hs⟩, hx⟩
        refine ⟨⟨k, hk, hs⟩, k, hk, hs, ?_⟩
        have hx' : walkVWord n ω = x := hx
        unfold walkVWord at hx'
        rwa [markTime_eq hk] at hx'
      · rintro ⟨hb, k, hk, hs, hx⟩
        refine ⟨hb, ?_⟩
        change walkVWord n ω = x
        unfold walkVWord
        rw [markTime_eq hk]
        exact hx
    rw [e1, e2]
    exact (prop_vervaatdiscrete μ.toMeasure hn x).symm
  calc ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ)
      = ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).map (wordPath B ∘ treeWord) :=
        Measure.map_congr hT
    _ = (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).map treeWord).map (wordPath B) :=
        (Measure.map_map measurable_from_top measurable_treeWord).symm
    _ = (((iidWalk μ)[|bridgeAtMark n]).map (walkVWord n)).map (wordPath B) := by rw [hwords]
    _ = ((iidWalk μ)[|bridgeAtMark n]).map (wordPath B ∘ walkVWord n) :=
        Measure.map_map measurable_from_top (measurable_walkVWord n)
    _ = ((iidWalk μ)[|bridgeAtMark n]).map
        (fun ω => Skorokhod.vervaatD (bridgeWalkPath B n ω)) :=
        (Measure.map_congr hW).symm

end BGWLeaves.LeafLimits.VervaatLaw
