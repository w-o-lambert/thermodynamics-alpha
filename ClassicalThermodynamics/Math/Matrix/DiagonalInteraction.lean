import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
namespace ClassicalThermodynamics.Math.Matrix

theorem diagonal_add_isSymm {ι : Type*} [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    (Matrix.diagonal d + A).IsSymm := by
  exact (Matrix.isSymm_diagonal d).add hA

theorem scalarDiagonal_add_mulVec_of_eigenpair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (q : ι → ℝ) (lambda alpha : ℝ)
    (hAq : Matrix.mulVec A q = lambda • q) :
    Matrix.mulVec (Matrix.diagonal (fun _ => alpha) + A) q =
      (alpha + lambda) • q := by
  funext i
  have hi := congrFun hAq i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  simp only [Matrix.add_mulVec, Pi.add_apply]
  have hdiag : Matrix.mulVec (Matrix.diagonal (fun _ : ι => alpha)) q i =
      alpha * q i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    simp
  rw [hdiag, hi]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end ClassicalThermodynamics.Math.Matrix
