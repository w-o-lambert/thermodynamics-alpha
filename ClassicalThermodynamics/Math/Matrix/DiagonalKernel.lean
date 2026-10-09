import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Math.Matrix

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Componentwise form of a kernel equation for a diagonal-plus-interaction matrix. -/
theorem diagonal_add_mulVec_eq_zero_iff
    (d q : ι → ℝ) (A : Matrix ι ι ℝ) :
    Matrix.mulVec (Matrix.diagonal d + A) q = 0 ↔
      ∀ i, d i * q i + ∑ j, A i j * q j = 0 := by
  have hdiag : ∀ i, Matrix.mulVec (Matrix.diagonal d) q i = d i * q i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    simp
  constructor
  · intro h i
    have hi := congrFun h i
    rw [Matrix.add_mulVec] at hi
    change Matrix.mulVec (Matrix.diagonal d) q i +
      (∑ j, A i j * q j) = 0 at hi
    rw [hdiag i] at hi
    exact hi
  · intro h
    funext i
    rw [Matrix.add_mulVec]
    change Matrix.mulVec (Matrix.diagonal d) q i +
      (∑ j, A i j * q j) = 0
    rw [hdiag i]
    exact h i

/-- Solving the componentwise kernel equation for the diagonal entry. -/
theorem diagonal_entry_eq_of_kernel
    (d q : ι → ℝ) (A : Matrix ι ι ℝ)
    (hkernel : Matrix.mulVec (Matrix.diagonal d + A) q = 0)
    (i : ι) (hqi : q i ≠ 0) :
    d i = -(∑ j, A i j * q j) / q i := by
  have hi := (diagonal_add_mulVec_eq_zero_iff d q A).mp hkernel i
  apply (eq_div_iff hqi).2
  linarith

/-- Conversely, diagonal entries reconstructed from a pointwise nonzero direction
make that direction a kernel vector. -/
theorem mulVec_eq_zero_of_diagonal_eq_ratio
    (d q : ι → ℝ) (A : Matrix ι ι ℝ)
    (hq : ∀ i, q i ≠ 0)
    (hd : ∀ i, d i = -(∑ j, A i j * q j) / q i) :
    Matrix.mulVec (Matrix.diagonal d + A) q = 0 := by
  apply (diagonal_add_mulVec_eq_zero_iff d q A).2
  intro i
  rw [hd i]
  field_simp [hq i]
  ring

end ClassicalThermodynamics.Math.Matrix
