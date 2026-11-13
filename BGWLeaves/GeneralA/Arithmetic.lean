module

public import BGWLeaves.GeneralA.Defs
public import BGWLeaves.LeafMass.Arithmetic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Arithmetic of the corrected lattice factor in Theorem 8.1(I). -/

@[expose] public section

open BGW.StableTrees

namespace BGWLeaves.GeneralA.Arithmetic

/-- There is a positive arithmetic generator, for every marking set. -/
theorem exists_pos_mem_arithSet {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) : ∃ r : ℕ, 0 < r ∧ (r : ℤ) ∈ arithSet μ A := by
  obtain ⟨k, hk, hμ⟩ := LeafMass.Arithmetic.exists_two_le hc hne
  by_cases hA : k ∈ A
  · exact ⟨k, by omega, k, hμ, Or.inl ⟨hA, rfl⟩⟩
  · refine ⟨k - 1, by omega, k, hμ, Or.inr ⟨hA, ?_⟩⟩
    omega

/-- The corrected arithmetic factor exists as a positive greatest common divisor. -/
theorem arithFactor_isGreatest {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ) :
    IsGreatest {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ A, (e : ℤ) ∣ s} (arithFactor μ A) := by
  obtain ⟨r, hr, hmem⟩ := exists_pos_mem_arithSet hc hne A
  have hne' : {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ A, (e : ℤ) ∣ s}.Nonempty :=
    ⟨1, by simp⟩
  have hfinite : {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ A, (e : ℤ) ∣ s}.Finite := by
    apply (Set.finite_Iic r).subset
    intro e he
    have hd := he.2 r hmem
    exact_mod_cast Int.le_of_dvd (by exact_mod_cast hr) hd
  exact hne'.isGreatest_csSup hfinite

/-- The arithmetic factor is positive. -/
theorem arithFactor_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ) :
    0 < arithFactor μ A :=
  lt_of_lt_of_le Nat.zero_lt_one (arithFactor_isGreatest hc hne A).1.1

/-- The arithmetic factor divides every element of `arithSet μ A`. -/
theorem arithFactor_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} {s : ℤ} (hs : s ∈ arithSet μ A) : (arithFactor μ A : ℤ) ∣ s :=
  (arithFactor_isGreatest hc hne A).1.2 s hs

/-- Every common divisor divides the corrected arithmetic factor. -/
theorem dvd_arithFactor {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ)
    {d : ℕ} (hd : ∀ s ∈ arithSet μ A, (d : ℤ) ∣ s) : d ∣ arithFactor μ A := by
  obtain ⟨r, hr, hmem⟩ := exists_pos_mem_arithSet hc hne A
  have hdpos : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    have hh := hd r hmem
    simp only [hz, Nat.cast_zero, zero_dvd_iff] at hh
    omega
  have he := arithFactor_pos hc hne A
  have hl : 1 ≤ Nat.lcm (arithFactor μ A) d := Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero he.ne' hdpos.ne')
  have hle : Nat.lcm (arithFactor μ A) d ≤ arithFactor μ A :=
    (arithFactor_isGreatest hc hne A).2 ⟨hl, fun s hs =>
      Int.coe_lcm_dvd_iff.mpr ⟨arithFactor_dvd hc hne hs, hd s hs⟩⟩
  have heq : Nat.lcm (arithFactor μ A) d = arithFactor μ A :=
    le_antisymm hle (Nat.le_of_dvd (by omega) (Nat.dvd_lcm_left _ _))
  exact heq ▸ Nat.dvd_lcm_right (arithFactor μ A) d

/-- If zero is unmarked, its increment `-1` forces arithmetic factor one. -/
theorem arithFactor_eq_one_of_zero_not_mem {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} (hA : 0 ∉ A) : arithFactor μ A = 1 := by
  have hd : (arithFactor μ A : ℤ) ∣ (-1 : ℤ) :=
    arithFactor_dvd hc hne ⟨0, LeafMass.Arithmetic.mu_zero_ne_zero hc hne,
      Or.inr ⟨hA, by simp⟩⟩
  have hd' : (arithFactor μ A : ℤ) ∣ (1 : ℤ) := by simpa using dvd_neg.mp hd
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd')

end BGWLeaves.GeneralA.Arithmetic
