module

public import BGWLeaves.LeafLimitsGeneral.DenominatorLattice
public import BGWLeaves.LeafLimitsGeneral.ShiftLattice
public import BGWLeaves.LeafLimits.Absolue

/-! Residue projection for the two leaf clocks. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.Residue
open Filter
open scoped Topology

/-- Projection onto `r + gℤ`, moving forward by less than one span. -/
def project (g : ℕ) (r z : ℤ) : ℤ := z + (r - z) % (g : ℤ)

theorem project_dvd (g : ℕ) (r z : ℤ) : (g : ℤ) ∣ r - project g r z := by
  convert (Int.dvd_self_sub_emod (x := r - z) (m := (g : ℤ))) using 1; dsimp [project]; ring

theorem project_eq_self {g : ℕ} {r z : ℤ} (h : (g : ℤ) ∣ r - z) :
    project g r z = z := by simp [project, Int.emod_eq_zero_of_dvd h]

theorem project_bounds {g : ℕ} (hg : 0 < g) (r z : ℤ) :
    z ≤ project g r z ∧ project g r z < z + g := by
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  have h0 := Int.emod_nonneg (r - z) hg'.ne'
  have h1 := Int.emod_lt_of_pos (r - z) hg'
  dsimp [project]
  omega

/-- Projecting a natural endpoint keeps it nonnegative. -/
def natProject (g : ℕ) (r : ℤ) (z : ℕ) : ℕ := (project g r z).toNat

theorem natProject_cast {g : ℕ} (hg : 0 < g) (r : ℤ) (z : ℕ) :
    (natProject g r z : ℤ) = project g r z := by
  exact Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg z) (project_bounds hg r z).1)

theorem natProject_dvd {g : ℕ} (hg : 0 < g) (r : ℤ) (z : ℕ) :
    (g : ℤ) ∣ r - natProject g r z := by rw [natProject_cast hg]; exact project_dvd g r z

theorem natProject_bounds {g : ℕ} (hg : 0 < g) (r : ℤ) (z : ℕ) :
    z ≤ natProject g r z ∧ natProject g r z < z + g := by
  have hb := project_bounds hg r z
  rw [← natProject_cast hg] at hb
  exact_mod_cast hb

/-- A bounded residue correction disappears under every diverging norming. -/
theorem project_normalized_tendsto {g : ℕ} (hg : 0 < g) {r z : ℕ → ℤ}
    {B : ℕ → ℝ} {x : ℝ} (hB : Tendsto B atTop atTop)
    (hz : Tendsto (fun n => (z n : ℝ) / B n) atTop (𝓝 x)) :
    Tendsto (fun n => (project g (r n) (z n) : ℝ) / B n) atTop (𝓝 x) := by
  have hsmall : Tendsto (fun n => (project g (r n) (z n) : ℝ) / B n - (z n : ℝ) / B n)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_nhds.div_atTop hB : Tendsto (fun n => (g : ℝ) / B n) atTop (𝓝 0))
    · filter_upwards [hB.eventually (eventually_gt_atTop 0)] with n hn
      have hb : (z n : ℝ) ≤ (project g (r n) (z n) : ℝ) := by exact_mod_cast (project_bounds hg (r n) (z n)).1
      exact sub_nonneg.2 (div_le_div_of_nonneg_right hb hn.le)
    · filter_upwards [hB.eventually (eventually_gt_atTop 0)] with n hn
      have hb : (project g (r n) (z n) : ℝ) - (z n : ℝ) ≤ g := by
        have hh := (project_bounds hg (r n) (z n)).2.le
        exact_mod_cast (show project g (r n) (z n) - z n ≤ (g : ℤ) by omega)
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hb hn.le
  simpa only [sub_add_cancel, zero_add] using hsmall.add hz

end BGWLeaves.LeafLimitsGeneral.Residue
