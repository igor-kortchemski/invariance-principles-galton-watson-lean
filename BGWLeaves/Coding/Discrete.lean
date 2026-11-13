module

public import BGWLeaves.Coding.Defs
public import BGW.Tree.DFS
public import BGW.Tree.Height
public import BGW.Tree.Excursion

/-!
# M11 provider `Discrete`

Provider for the discrete coding facts: the registered holes `prop_Hmes`,
`intro_enc_lukasiewicz_end` and `intro_enc_lukasiewicz_injective` of `BGWLeaves.Coding`, exported in
namespace `BGWLeaves.Coding.Discrete` with exactly the types of the statements file.
-/

@[expose] public section

namespace BGWLeaves.Coding.Discrete

open BGW

/-- The proposition of line 515 (`eq:Hmes`): BGW's `PlaneTree.height_eq_card_recordMin`. -/
theorem prop_Hmes (t : PlaneTree) (i : Fin t.size) :
    t.height i = ((Finset.range i.val).filter
      (fun j => ∀ k, j ≤ k → k ≤ i.val → t.lukasiewicz j ≤ t.lukasiewicz k)).card :=
  PlaneTree.height_eq_card_recordMin t i

/-- `intro:enc` (line 496): `W_{ζ(τ)}(τ) = -1`. -/
theorem intro_enc_lukasiewicz_end (t : PlaneTree) : t.lukasiewicz t.size = -1 := by
  rw [PlaneTree.lukasiewicz, ← PlaneTree.length_increments, List.take_length]
  exact PlaneTree.sum_increments t

/-- `intro:enc` (lines 226-232): the Łukasiewicz increment word determines the tree. -/
theorem intro_enc_lukasiewicz_injective :
    Function.Injective (fun t : PlaneTree => t.increments) :=
  PlaneTree.increments_injective

end BGWLeaves.Coding.Discrete
