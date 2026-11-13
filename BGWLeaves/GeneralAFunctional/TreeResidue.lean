module

public import BGWLeaves.GeneralAFunctional.TreeLocal
public import BGWLeaves.LeafLimitsGeneral.Residue

/-! The pending-tree residue includes the revealed mark count. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeResidue

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeLocal
open scoped ENNReal Topology Classical

/-- The arithmetic contribution of a prefix is its walk endpoint plus its marks. -/
theorem prefix_arithmetic {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (ha : ∀ d ∈ a, μ d ≠ 0) :
    (arithFactor μ A : ℤ) ∣ prefixWalk a + (prefixMarks A a : ℤ) := by
  induction a with
  | nil => simp [prefixWalk, prefixMarks]
  | cons d a ih =>
    have hd : ∀ {s : ℤ}, s ∈ arithSet μ A → (arithFactor μ A : ℤ) ∣ s :=
      fun h => GeneralA.Arithmetic.arithFactor_dvd hc hne h
    have hi := ih (fun k hk => ha k (List.mem_cons_of_mem d hk))
    have hdμ := ha d List.mem_cons_self
    by_cases hdA : d ∈ A
    · have hstep : (arithFactor μ A : ℤ) ∣ (d : ℤ) :=
        hd ⟨d, hdμ, Or.inl ⟨hdA, rfl⟩⟩
      have h := hstep.add hi
      convert h using 1
      simp [prefixWalk, prefixMarks, hdA]
      ring
    · have hstep : (arithFactor μ A : ℤ) ∣ (d : ℤ) - 1 :=
        hd ⟨d, hdμ, Or.inr ⟨hdA, rfl⟩⟩
      have h := hstep.add hi
      convert h using 1
      simp [prefixWalk, prefixMarks, hdA]
      ring

/-- Every supported surviving prefix of an admissible target has the pending-tree residue. -/
theorem pending_residue {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} {n : ℕ} (hn : ZetaAAdmissible μ A n)
    {a : List ℕ} (hs : IsSurvivingPrefix a) (ha : ∀ d ∈ a, μ d ≠ 0)
    (hkn : prefixMarks A a ≤ n) :
    (arithFactor μ A : ℤ) ∣ ((n - prefixMarks A a : ℕ) : ℤ) - prefixStack a := by
  have hd := (admissible_dvd hc hne hn).sub (prefix_arithmetic hc hne A a ha)
  rw [prefixStack_cast hs, Nat.cast_sub hkn]
  convert hd using 1
  ring

/-- Project a candidate endpoint onto the residue selected by the remaining marks. -/
def pendingProject (e n k j : ℕ) : ℕ :=
  LeafLimitsGeneral.Residue.natProject e ((n - k : ℕ) : ℤ) j

theorem pendingProject_eq {e n k j : ℕ} (_he : 0 < e)
    (hr : (e : ℤ) ∣ ((n - k : ℕ) : ℤ) - j) : pendingProject e n k j = j := by
  unfold pendingProject LeafLimitsGeneral.Residue.natProject
  rw [LeafLimitsGeneral.Residue.project_eq_self hr, Int.toNat_natCast]

theorem pendingProject_residue {e : ℕ} (he : 0 < e) (n k j : ℕ) :
    (e : ℤ) ∣ ((n - k : ℕ) : ℤ) - pendingProject e n k j :=
  LeafLimitsGeneral.Residue.natProject_dvd he _ _

theorem pendingProject_prefix {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} {n : ℕ} (hn : ZetaAAdmissible μ A n)
    {a : List ℕ} (hs : IsSurvivingPrefix a) (ha : ∀ d ∈ a, μ d ≠ 0)
    (hkn : prefixMarks A a ≤ n) :
    pendingProject (arithFactor μ A) n (prefixMarks A a) (prefixStack a) = prefixStack a :=
  pendingProject_eq (GeneralA.Arithmetic.arithFactor_pos hc hne A)
    (pending_residue hc hne hn hs ha hkn)

/-- Arbitrarily moving mark residues change a normalized endpoint by `o(1)`. -/
theorem pendingProject_normalized_tendsto {e : ℕ} (he : 0 < e)
    {n k j : ℕ → ℕ} {c : ℕ → ℝ} {x : ℝ} (hc : Tendsto c atTop atTop)
    (hj : Tendsto (fun i => (j i : ℝ) / c i) atTop (𝓝 x)) :
    Tendsto (fun i => (pendingProject e (n i) (k i) (j i) : ℝ) / c i) atTop (𝓝 x) := by
  have ht := LeafLimitsGeneral.Residue.project_normalized_tendsto he
    (r := fun i => ((n i - k i : ℕ) : ℤ)) (z := fun i => (j i : ℤ)) hc (by simpa using hj)
  convert ht using 1
  funext i
  rw [← LeafLimitsGeneral.Residue.natProject_cast he]
  simp only [Int.cast_natCast]
  rfl

end BGWLeaves.GeneralAFunctional.TreeResidue
