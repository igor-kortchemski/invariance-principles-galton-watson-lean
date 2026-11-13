module

public import BGWLeaves.GeneralAFunctional.TreePrefix

/-! Prefix atoms and the marked-to-total-tail density. These identities concern
surviving prefixes; they make no assertion that the density has total mass one. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeDensity

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralAFunctional.TreePrefix
open scoped ENNReal Classical

/-- Real mass of the marked conditioning event, including finite vertices. -/
noncomputable def markedMass (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  (bienaymeLaw μ.toMeasure).real {T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}

/-- The remaining forest mass, zero when the revealed marks already exceed `n`. -/
noncomputable def remainingMass (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) (a : List ℕ) : ℝ :=
  if prefixMarks A a ≤ n then
    ((Measure.pi fun _ : Fin (prefixStack a) => bienaymeLaw μ.toMeasure)
      (markedForestEvent A (prefixStack a) (n - prefixMarks A a))).toReal else 0

theorem markedMass_pos {μ : PMF ℕ} {A : Set ℕ} {n : ℕ} (hn : ZetaAAdmissible μ A n) :
    0 < markedMass μ A n :=
  ENNReal.toReal_pos hn (measure_ne_top _ _)

/-- Conditional marked prefix atom. -/
theorem markedPrefixMass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (n : ℕ) (hn : ZetaAAdmissible μ A n)
    (hs : IsSurvivingPrefix a) :
    (zetaATreeLaw μ A n).toMeasure.real (prefixCylinder a.length a) =
      degreeWeight μ a * remainingMass μ A n a / markedMass μ A n := by
  rw [coe_zetaATreeLaw hn, measureReal_def,
    cond_apply' (measurableSet_prefixCylinder _ _), ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (markedMass μ A n)⁻¹ *
    (bienaymeLaw μ.toMeasure).real
      ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩ prefixCylinder a.length a) = _
  rw [zetaAEvent_prefixCylinder_real μ hc hne A a n hs]
  change (markedMass μ A n)⁻¹ * (degreeWeight μ a * remainingMass μ A n a) = _
  ring

/-- RN weight against the existing inclusive total-size-tail tree law. -/
noncomputable def prefixDensity (μ : PMF ℕ) (A : Set ℕ) (n r : ℕ) (a : List ℕ) : ℝ :=
  forestTail μ 1 r / markedMass μ A n *
    (remainingMass μ A n a / forestTail μ (prefixStack a) (r - a.length))

/-- Exact prefix-atom form of the marked-to-total-tail RN identity (E).
Only surviving cylinders occur; the missing target mass must be controlled separately. -/
theorem markedPrefixMass_eq_density_mul (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (n r : ℕ) (hn : ZetaAAdmissible μ A n)
    (har : a.length < r) (hs : IsSurvivingPrefix a)
    (hG : 0 < forestTail μ (prefixStack a) (r - a.length)) :
    (zetaATreeLaw μ A n).toMeasure.real (prefixCylinder a.length a) =
      prefixDensity μ A n r a *
        (tailTreeLaw μ r).toMeasure.real (prefixCylinder a.length a) := by
  have hG1 := forestTail_pos μ hc hne r
  have hn0 := (markedMass_pos hn).ne'
  rw [markedPrefixMass μ hc hne A a n hn hs,
    tailPrefixMass μ hc hne rfl har hs hG1, prefixDensity]
  field_simp [hn0, hG.ne', hG1.ne']

end BGWLeaves.GeneralAFunctional.TreeDensity
