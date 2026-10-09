import ClassicalThermodynamics.Math.LinearAlgebra.Reflection2D

namespace ClassicalThermodynamics.Bridges

/-- Coordinate-rescaled presentation of the two-dimensional Householder
reflection. This is a representation in a scaled basis, not a separate
geometrical operation. -/
noncomputable def rescaledReflection2D (lx ly b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = 0 ∧ j = 0 then (lx^2 - ly^2) / (lx^2 + ly^2)
  else if i = 0 ∧ j = 1 then b * (2 * lx * ly / (lx^2 + ly^2))
  else if i = 1 ∧ j = 0 then b⁻¹ * (2 * lx * ly / (lx^2 + ly^2))
  else (ly^2 - lx^2) / (lx^2 + ly^2)

/-- Under `D A D⁻¹`, with `D = diag(1,b)`, the rescaled representation becomes
the canonical `Fin 2` Householder reflection. The nonzero-axis hypothesis is
explicit because `householder 0 = I`, whereas the displayed rational coordinate
formula is meaningful only for a nonzero reflection axis. -/
theorem rescaledReflection2D_coordinate_transform
    (lx ly b : ℝ) (hb : b ≠ 0) (haxis : lx^2 + ly^2 ≠ 0) :
    (fun i j => (![1, b] i) * rescaledReflection2D lx ly b i j / (![1, b] j)) =
      ClassicalThermodynamics.Math.LinearAlgebra.reflection2D lx ly := by
  funext i j
  rw [ClassicalThermodynamics.Math.LinearAlgebra.reflection2D_apply lx ly haxis i j]
  fin_cases i <;> fin_cases j
  · simp [rescaledReflection2D]
  · simp [rescaledReflection2D, hb]
  · simp [rescaledReflection2D, hb]
  · simp [rescaledReflection2D, hb]

end ClassicalThermodynamics.Bridges
