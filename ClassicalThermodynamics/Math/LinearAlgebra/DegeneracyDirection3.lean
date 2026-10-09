import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation

namespace ClassicalThermodynamics.Math.LinearAlgebra

/-- Three-coordinate degeneracy direction used by the binary virial-coefficient
families, ordered as `(B11,B12,B22)`. -/
noncomputable def degeneracyDirection3 (S : ℝ) : Fin 3 → ℝ := ![1, S, S⁻¹]

@[simp] theorem degeneracyDirection3_zero (S : ℝ) : degeneracyDirection3 S 0 = 1 := rfl
@[simp] theorem degeneracyDirection3_one (S : ℝ) : degeneracyDirection3 S 1 = S := rfl
@[simp] theorem degeneracyDirection3_two (S : ℝ) : degeneracyDirection3 S 2 = S⁻¹ := rfl

end ClassicalThermodynamics.Math.LinearAlgebra
