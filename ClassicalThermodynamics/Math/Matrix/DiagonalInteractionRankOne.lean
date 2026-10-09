import ClassicalThermodynamics.Math.Matrix.DiagonalInteraction
import ClassicalThermodynamics.Math.Matrix.DiagonalKernel

namespace ClassicalThermodynamics.Math.Matrix

open scoped BigOperators

noncomputable def rankOne {ι : Type*} (alpha : ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => alpha * u i * u j

noncomputable def diagonalInteractionRankOne
    {ι : Type*} [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) (alpha : ℝ) (u : ι → ℝ) :
    Matrix ι ι ℝ := Matrix.diagonal d + A + rankOne alpha u

@[simp] theorem rankOne_apply {ι : Type*}
    (alpha : ℝ) (u : ι → ℝ) (i j : ι) :
    rankOne alpha u i j = alpha * u i * u j := rfl

theorem rankOne_isSymm {ι : Type*} (alpha : ℝ) (u : ι → ℝ) :
    (rankOne alpha u).IsSymm := by
  ext i j
  change alpha * u j * u i = alpha * u i * u j
  ring

theorem diagonalInteractionRankOne_isSymm
    {ι : Type*} [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) (alpha : ℝ) (u : ι → ℝ)
    (hA : A.IsSymm) :
    (diagonalInteractionRankOne d A alpha u).IsSymm := by
  exact (diagonal_add_isSymm d A hA).add (rankOne_isSymm alpha u)

theorem rankOne_mulVec {ι : Type*} [Fintype ι]
    (alpha : ℝ) (u q : ι → ℝ) :
    Matrix.mulVec (rankOne alpha u) q =
      (alpha * dotProduct u q) • u := by
  funext i
  unfold rankOne Matrix.mulVec dotProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j, alpha * u i * u j * q j) =
      (alpha * u i) * ∑ j, u j * q j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  ring

theorem diagonalInteractionRankOne_mulVec_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d q : ι → ℝ) (A : Matrix ι ι ℝ) (alpha : ℝ) (u : ι → ℝ) :
    Matrix.mulVec (diagonalInteractionRankOne d A alpha u) q = 0 ↔
      ∀ i, d i * q i + ∑ j, A i j * q j +
        alpha * u i * dotProduct u q = 0 := by
  have hdiag : ∀ i, Matrix.mulVec (Matrix.diagonal d) q i = d i * q i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    simp
  unfold diagonalInteractionRankOne
  rw [Matrix.add_mulVec, rankOne_mulVec]
  constructor
  · intro h i
    have hi := congrFun h i
    rw [Matrix.add_mulVec] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    change Matrix.mulVec (Matrix.diagonal d) q i +
      (∑ j, A i j * q j) + alpha * dotProduct u q * u i = 0 at hi
    rw [hdiag i] at hi
    simpa [mul_assoc, mul_left_comm, mul_comm] using hi
  · intro h
    funext i
    rw [Matrix.add_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change Matrix.mulVec (Matrix.diagonal d) q i +
      (∑ j, A i j * q j) + alpha * dotProduct u q * u i = 0
    rw [hdiag i]
    simpa [mul_assoc, mul_left_comm, mul_comm] using h i

end ClassicalThermodynamics.Math.Matrix
