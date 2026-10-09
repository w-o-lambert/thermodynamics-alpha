import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
open Matrix
namespace ClassicalThermodynamics.Math
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem det_eq_zero_of_mulVec_eq_zero (A : Matrix ι ι ℝ) (q : ι → ℝ)
    (hq : q ≠ 0) (hAq : A *ᵥ q = 0) : A.det = 0 := by
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨q, hq, hAq⟩
end ClassicalThermodynamics.Math
