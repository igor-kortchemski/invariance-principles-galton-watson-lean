module

public import BGWLeaves.GeneralAFunctional.TreeEvents
public import BGW.StableTrees.ExactContourBasic
public import BGWLeaves.LeafConcentration.Defs

/-! Mirror invariance for arbitrary offspring-mark conditioning. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeMirror

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.GeneralA.Marked BGWLeaves.GeneralA.MarkedLaw
open scoped ENNReal NNReal Topology Classical

theorem bienaymeLaw_finiteTreeEvent_eq_tsum (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (Q : PlaneTree → Prop) :
    LocallyFinite.bienaymeLaw ν (BGWLeaves.finiteTreeEvent Q) =
      ∑' t : PlaneTree, if Q t then PlaneTree.weight (fun d => ν {d}) t else 0 := by
  have hA : MeasurableSet (BGWLeaves.finiteTreeEvent Q) := by
    have hEq : BGWLeaves.finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t : PlaneTree | Q t} := by
      ext T
      simp only [BGWLeaves.finiteTreeEvent, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨t, rfl, ht⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, rfl, ht⟩
    rw [hEq]
    exact (Set.to_countable _).image _ |>.measurableSet
  have hsub : BGWLeaves.finiteTreeEvent Q ⊆ {T : LocallyFinite.Tree | FiniteVertices T} := by
    rintro T ⟨t, rfl, -⟩
    exact t.finiteVertices_toLocallyFinite
  have h : LocallyFinite.bienaymeLaw ν (BGWLeaves.finiteTreeEvent Q) =
      (LocallyFinite.bienaymeLaw ν).restrict {T : LocallyFinite.Tree | FiniteVertices T}
        (BGWLeaves.finiteTreeEvent Q) := by
    rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub]
  rw [h, LocallyFinite.bienaymeLaw_restrict_finiteVertices, Measure.sum_apply _ hA]
  refine tsum_congr fun t => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases ht : Q t
  · have hmem : t.toLocallyFinite ∈ BGWLeaves.finiteTreeEvent Q := ⟨t, rfl, ht⟩
    simp [hmem, ht]
  · have hmem : t.toLocallyFinite ∉ BGWLeaves.finiteTreeEvent Q := by
      rintro ⟨s, hs, hq⟩
      exact ht (PlaneTree.toLocallyFinite_injective hs ▸ hq)
    simp [hmem, ht]


theorem treeACount_mirror (A : Set ℕ) (t : PlaneTree) :
    treeACount A t.mirror = treeACount A t := by
  induction t with
  | node ts ih =>
    simp only [treeACount, PlaneTree.mirror_node, PlaneTree.degrees_node,
      List.length_reverse, List.length_map, List.countP_cons, List.countP_flatten,
      List.map_reverse, List.sum_reverse, List.map_map]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun t ht => ih t ht)

theorem map_treeMirror_zetaATreeLaw {μ : PMF ℕ} {A : Set ℕ} {n : ℕ}
    (hn : ZetaAAdmissible μ A n) :
    (zetaATreeLaw μ A n).map ExactContour.treeMirror = zetaATreeLaw μ A n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, coe_zetaATreeLaw hn]
  ext D hD
  rw [Measure.map_apply ExactContour.measurable_treeMirror hD,
    cond_apply (measurableSet_zetaAEvent A n), cond_apply (measurableSet_zetaAEvent A n)]
  congr 1
  have heq (E : Set LocallyFinite.Tree) :
      {T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩ E =
        finiteTreeEvent (fun t => treeACount A t = n ∧ t.toLocallyFinite ∈ E) := by
    ext T
    constructor
    · rintro ⟨⟨hT, hcnt⟩, hE⟩
      obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT
      rw [zetaA_toLocallyFinite] at hcnt
      exact ⟨t, rfl, ENat.natCast_inj.mp hcnt, hE⟩
    · rintro ⟨t, rfl, hcnt, hE⟩
      exact ⟨⟨t.finiteVertices_toLocallyFinite, by rw [zetaA_toLocallyFinite, hcnt]⟩, hE⟩
  rw [heq, heq, bienaymeLaw_finiteTreeEvent_eq_tsum, bienaymeLaw_finiteTreeEvent_eq_tsum]
  let e : PlaneTree ≃ PlaneTree :=
    ⟨PlaneTree.mirror, PlaneTree.mirror, PlaneTree.mirror_mirror, PlaneTree.mirror_mirror⟩
  rw [← e.tsum_eq]
  apply tsum_congr
  intro t
  simp only [e, Equiv.coe_fn_mk, treeACount_mirror, Set.mem_preimage,
    ExactContour.treeMirror_toLocallyFinite, PlaneTree.mirror_mirror, PlaneTree.weight_mirror]
  by_cases hh : treeACount A t = n ∧ t.toLocallyFinite ∈ D <;> simp only [hh, ↓reduceIte]

end BGWLeaves.GeneralAFunctional.TreeMirror
