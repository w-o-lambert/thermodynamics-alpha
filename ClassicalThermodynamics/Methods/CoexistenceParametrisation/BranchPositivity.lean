import ClassicalThermodynamics.Methods.CoexistenceParametrisation.BranchDomain
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ClassicalThermodynamics.Methods.CoexistenceParametrisation

noncomputable def vdwMidpointNumeratorAux (x : ℝ) : ℝ :=
  x * Real.cosh x - Real.sinh x

theorem hasDerivAt_vdwMidpointNumeratorAux (x : ℝ) :
    HasDerivAt vdwMidpointNumeratorAux (x * Real.sinh x) x := by
  unfold vdwMidpointNumeratorAux
  convert (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
    (Real.hasDerivAt_sinh x)) using 1
  · rfl
  · simp only [one_mul, id_eq]
    ring

theorem vdwMidpointNumeratorAux_pos {x : ℝ} (hx : 0 < x) :
    0 < vdwMidpointNumeratorAux x := by
  have hcont : ContinuousOn vdwMidpointNumeratorAux (Set.Ici (0 : ℝ)) := by
    exact ((continuous_id.mul Real.continuous_cosh).sub
      Real.continuous_sinh).continuousOn
  have hderiv : ∀ y ∈ interior (Set.Ici (0 : ℝ)),
      0 < deriv vdwMidpointNumeratorAux y := by
    intro y hy
    have hypos : 0 < y := by simpa using hy
    rw [(hasDerivAt_vdwMidpointNumeratorAux y).deriv]
    exact mul_pos hypos (Real.sinh_pos_iff.mpr hypos)
  have hmono : StrictMonoOn vdwMidpointNumeratorAux (Set.Ici (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont hderiv
  have hlt := hmono (by simp) (by exact le_of_lt hx) hx
  simpa [vdwMidpointNumeratorAux] using hlt

theorem vdwGeometricMidpoint_numerator_pos {d : ℝ} (hd : 0 < d) :
    0 < d * Real.cosh (d / 2) - 2 * Real.sinh (d / 2) := by
  have hhalf : 0 < d / 2 := by linarith
  have h := vdwMidpointNumeratorAux_pos hhalf
  unfold vdwMidpointNumeratorAux at h
  nlinarith

theorem vdwGeometricMidpoint_denominator_pos {d : ℝ} (hd : 0 < d) :
    0 < Real.sinh d - d := by
  exact sub_pos.mpr (Real.self_lt_sinh_iff.mpr hd)

theorem vdwGeometricMidpoint_pos {d : ℝ} (hd : 0 < d) :
    0 < vdwGeometricMidpoint d := by
  rw [vdwGeometricMidpoint_eq_formula (ne_of_gt hd)]
  unfold vdwGeometricMidpointFormula
  exact div_pos (vdwGeometricMidpoint_numerator_pos hd)
    (vdwGeometricMidpoint_denominator_pos hd)

theorem physicalBranchParameter_of_pos {d : ℝ} (hd : 0 < d) :
    PhysicalBranchParameter d :=
  ⟨hd, vdwGeometricMidpoint_pos hd⟩

end ClassicalThermodynamics.Methods.CoexistenceParametrisation
