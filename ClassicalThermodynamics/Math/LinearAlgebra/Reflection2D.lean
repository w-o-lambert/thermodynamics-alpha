import ClassicalThermodynamics.Math.LinearAlgebra.Householder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Math.LinearAlgebra

/-- Two-dimensional reflection fixing the axis `(lx,ly)`.  This is not an
independent implementation: it is the `Fin 2` Householder reflection whose
normal direction is `(-ly,lx)`. -/
noncomputable def reflection2D (lx ly : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  householder ![-ly, lx]

/-- Entrywise formula traditionally used for the two-dimensional reflection. -/
theorem reflection2D_apply (lx ly : ℝ) (h : lx^2 + ly^2 ≠ 0)
    (i j : Fin 2) :
    reflection2D lx ly i j =
      if i = 0 ∧ j = 0 then (lx^2 - ly^2) / (lx^2 + ly^2)
      else if i = 0 ∧ j = 1 then 2 * lx * ly / (lx^2 + ly^2)
      else if i = 1 ∧ j = 0 then 2 * lx * ly / (lx^2 + ly^2)
      else (ly^2 - lx^2) / (lx^2 + ly^2) := by
  have h' : ly * ly + lx * lx ≠ 0 := by
    intro hz
    apply h
    nlinarith [sq_nonneg lx, sq_nonneg ly]
  have hdot : dotProduct ![-ly, lx] ![-ly, lx] = lx^2 + ly^2 := by
    simp [dotProduct, Fin.sum_univ_two]
    ring
  fin_cases i <;> fin_cases j
  · change 1 - 2 * (-ly) * (-ly) / dotProduct ![-ly, lx] ![-ly, lx] =
      (lx^2 - ly^2) / (lx^2 + ly^2)
    rw [hdot]
    field_simp [h]
    ring
  · change 0 - 2 * (-ly) * lx / dotProduct ![-ly, lx] ![-ly, lx] =
      2 * lx * ly / (lx^2 + ly^2)
    rw [hdot]
    field_simp [h]
    ring
  · change 0 - 2 * lx * (-ly) / dotProduct ![-ly, lx] ![-ly, lx] =
      2 * lx * ly / (lx^2 + ly^2)
    rw [hdot]
    field_simp [h]
    ring
  · change 1 - 2 * lx * lx / dotProduct ![-ly, lx] ![-ly, lx] =
      (ly^2 - lx^2) / (lx^2 + ly^2)
    rw [hdot]
    field_simp [h]
    ring

/-- `reflection2D` is exactly the indicated Householder specialization. -/
@[simp] theorem reflection2D_eq_householder (lx ly : ℝ) :
    reflection2D lx ly = householder ![-ly, lx] := rfl

/-- The reflection fixes its axis direction. -/
theorem reflection2D_mulVec_axis (lx ly : ℝ) (_h : lx^2 + ly^2 ≠ 0) :
    Matrix.mulVec (reflection2D lx ly) ![lx, ly] = ![lx, ly] := by
  apply householder_mulVec_of_orthogonal
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- The active direction perpendicular to the axis is reversed. -/
theorem reflection2D_mulVec_perp (lx ly : ℝ) (h : lx^2 + ly^2 ≠ 0) :
    Matrix.mulVec (reflection2D lx ly) ![-ly, lx] = - ![-ly, lx] := by
  unfold reflection2D
  apply householder_mulVec_direction
  simp [dotProduct, Fin.sum_univ_two]
  intro hz
  apply h
  nlinarith [sq_nonneg lx, sq_nonneg ly]

end ClassicalThermodynamics.Math.LinearAlgebra
