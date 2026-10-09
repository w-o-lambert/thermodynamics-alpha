import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Math.LinearAlgebra
open scoped BigOperators

/-- Householder reflection `I - 2 uuᵀ/(u·u)` associated with a finite direction.
The nonzero hypothesis is imposed by the theorems that require a genuine
reflection, rather than hidden in the definition. -/
noncomputable def householder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then 1 else 0) -
    2 * u i * u j / dotProduct u u

/-- The Householder matrix is symmetric. -/
theorem householder_isSymm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) :
    (householder u).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, householder]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ite_false]
    ring

/-- A Householder reflection reverses its defining direction. -/
theorem householder_mulVec_direction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : dotProduct u u ≠ 0) :
    Matrix.mulVec (householder u) u = -u := by
  funext i
  simp only [householder, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib]
  rw [show (∑ j, (if i = j then 1 else 0) * u j) = u i by simp]
  have hsum :
      (∑ j, (2 * u i * u j / ∑ k, u k * u k) * u j) = 2 * u i := by
    rw [show (∑ j, (2 * u i * u j / ∑ k, u k * u k) * u j) =
        (2 * u i / ∑ k, u k * u k) * ∑ j, u j * u j by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
    exact div_mul_cancel₀ (2 * u i) hu
  rw [hsum]
  change u i - 2 * u i = -u i
  ring

/-- Every vector orthogonal to the defining direction is fixed. -/
theorem householder_mulVec_of_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (huv : dotProduct u v = 0) :
    Matrix.mulVec (householder u) v = v := by
  funext i
  change (∑ j, ((if i = j then 1 else 0) -
    2 * u i * u j / dotProduct u u) * v j) = v i
  rw [Finset.sum_congr rfl (fun j _ => by rw [sub_mul]),
    Finset.sum_sub_distrib]
  have hdiag : (∑ j, (if i = j then 1 else 0) * v j) = v i := by
    simp
  rw [hdiag]
  have hsum :
      (∑ j, (2 * u i * u j / dotProduct u u) * v j) =
        (2 * u i / dotProduct u u) * dotProduct u v := by
    unfold dotProduct
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum, huv]
  ring

end ClassicalThermodynamics.Math.LinearAlgebra
