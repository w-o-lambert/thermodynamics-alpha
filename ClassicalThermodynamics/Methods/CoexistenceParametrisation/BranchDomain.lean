import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Physical branch domain. The analytically difficult fact is positivity of the
closed midpoint scale; all denominator consequences are derived from it. -/
def PhysicalBranchParameter (d : ℝ) : Prop :=
  0 < d ∧ 0 < vdwGeometricMidpoint d

theorem vdwBranches_pos {d : ℝ} (hd : PhysicalBranchParameter d) :
    0 < vdwLiquidFreeVolume d ∧ 0 < vdwGasFreeVolume d := by
  constructor
  · unfold vdwLiquidFreeVolume
    exact mul_pos hd.2 (Real.exp_pos _)
  · unfold vdwGasFreeVolume
    exact mul_pos hd.2 (Real.exp_pos _)

/-- The two branches are distinct for a strictly positive branch parameter. -/
theorem vdwGasFreeVolume_lt_vdwLiquidFreeVolume {d : ℝ} (hd : PhysicalBranchParameter d) :
    vdwGasFreeVolume d < vdwLiquidFreeVolume d := by
  unfold vdwLiquidFreeVolume vdwGasFreeVolume
  have he : Real.exp (-d / 2) < Real.exp (d / 2) := by
    exact Real.exp_lt_exp.mpr (by linarith [hd.1])
  exact mul_lt_mul_of_pos_left he hd.2

/-- All elementary free-volume denominators are nonzero on the physical branch. -/
theorem physicalBranch_denominators {d : ℝ} (hd : PhysicalBranchParameter d) :
    vdwLiquidFreeVolume d ≠ 0 ∧ vdwGasFreeVolume d ≠ 0 ∧
    1 + vdwLiquidFreeVolume d ≠ 0 ∧ 1 + vdwGasFreeVolume d ≠ 0 ∧
    vdwLiquidFreeVolume d - vdwGasFreeVolume d ≠ 0 ∧
    vdwLiquidFreeVolume d + vdwGasFreeVolume d + 2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d ≠ 0 := by
  rcases vdwBranches_pos hd with ⟨hH, hL⟩
  have hlt := vdwGasFreeVolume_lt_vdwLiquidFreeVolume hd
  constructor
  · exact ne_of_gt hH
  constructor
  · exact ne_of_gt hL
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · linarith
  · positivity

/-- The quotient hypotheses used by the closed coexistence proof follow from the
physical branch assumptions, except for the defining `sinh d - d` denominator. -/
theorem physicalBranch_quotient_factors {d : ℝ}
    (hd : PhysicalBranchParameter d) :
    vdwGeometricMidpoint d ≠ 0 ∧
    2 * vdwGeometricMidpoint d * Real.sinh (d / 2) ≠ 0 ∧
    2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
      2 * (vdwGeometricMidpoint d)^2 ≠ 0 := by
  have hs : 0 < Real.sinh (d / 2) :=
    Real.sinh_pos_iff.mpr (by linarith [hd.1])
  have hc : 0 < Real.cosh (d / 2) := Real.cosh_pos _
  constructor
  · exact ne_of_gt hd.2
  constructor
  · exact ne_of_gt
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd.2) hs)
  · exact ne_of_gt
      (add_pos
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd.2) hc)
        (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hd.2)))

end ClassicalThermodynamics.Methods.CoexistenceParametrisation
