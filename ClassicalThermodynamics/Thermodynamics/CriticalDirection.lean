import ClassicalThermodynamics.Math.Matrix.RowReplacement

open scoped BigOperators

namespace ClassicalThermodynamics.Thermodynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric third-derivative tensor is represented as a trilinear coefficient
array. The present determinant argument only needs the contraction, not symmetry. -/
abbrev ThirdDerivativeTensor := ι → ι → ι → ℝ

/-- Contract the last two indices of the third derivative with a direction `q`.
For a free energy `F`, this is the row vector
`k_i = Σ_j Σ_l (∂³F/∂x_i∂x_j∂x_l) q_j q_l`. -/
noncomputable def thirdDerivativeContraction
    (T : ThirdDerivativeTensor (ι := ι)) (q : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, ∑ l, T i j l * q j * q l

/-- Third directional derivative along `q`.
It is `q · k`, where `k` is the contracted third-derivative row. -/
noncomputable def thirdDirectionalDerivative
    (T : ThirdDerivativeTensor (ι := ι)) (q : ι → ℝ) : ℝ :=
  dotProduct q (thirdDerivativeContraction T q)

omit [DecidableEq ι] in
/-- The scalar third-directional condition is the orthogonality condition required
for the replacement row in the `M₂` determinant. -/
theorem contraction_dot_direction
    (T : ThirdDerivativeTensor (ι := ι)) (q : ι → ℝ) :
    dotProduct (thirdDerivativeContraction T q) q =
      thirdDirectionalDerivative T q := by
  unfold thirdDirectionalDerivative dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  ring
/-- Coordinate-free critical-point data: a nonzero Hessian null direction and a
vanishing third directional derivative along that same direction. -/
structure CriticalDirectionData (H : Matrix ι ι ℝ)
    (T : ThirdDerivativeTensor (ι := ι)) where
  direction : ι → ℝ
  direction_ne_zero : direction ≠ 0
  hessian_kernel : Matrix.mulVec H direction = 0
  third_directional_zero : thirdDirectionalDerivative T direction = 0

/-- The Reid--Beegle row-replaced matrix associated with a selected row `r`. -/
noncomputable def criticalAugmentedMatrix
    (H : Matrix ι ι ℝ)
    (T : ThirdDerivativeTensor (ι := ι))
    (q : ι → ℝ) (r : ι) : Matrix ι ι ℝ :=
  ClassicalThermodynamics.Math.Matrix.replaceRow H r
    (thirdDerivativeContraction T q)

/-- Abstract `M₂` theorem.

If `H q = 0` and the third directional derivative along `q` vanishes, then replacing
any one row of `H` by the contracted third-derivative row gives a singular matrix.
This is the algebraic content behind the Reid--Beegle determinant criterion. -/
theorem det_criticalAugmentedMatrix_eq_zero
    [Nonempty ι]
    (H : Matrix ι ι ℝ)
    (T : ThirdDerivativeTensor (ι := ι))
    (d : CriticalDirectionData H T)
    (r : ι) :
    (criticalAugmentedMatrix H T d.direction r).det = 0 := by
  apply ClassicalThermodynamics.Math.Matrix.det_replaceRow_eq_zero_of_kernel
      H r (thirdDerivativeContraction T d.direction) d.direction
      d.direction_ne_zero d.hessian_kernel
  rw [contraction_dot_direction]
  exact d.third_directional_zero

end ClassicalThermodynamics.Thermodynamics

namespace ClassicalThermodynamics.Thermodynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Converse Reid--Beegle theorem under the explicit non-degeneracy condition
appropriate to replacement of row `r`.

If the unchanged Hessian rows have only the direction `q` as a common solution,
`q r ≠ 0`, and the augmented matrix is singular, then the third directional
derivative along `q` vanishes. -/
theorem thirdDirectionalDerivative_eq_zero_of_det_criticalAugmentedMatrix_eq_zero
    [Nonempty ι]
    (H : Matrix ι ι ℝ)
    (T : ThirdDerivativeTensor (ι := ι))
    (q : ι → ℝ) (r : ι)
    (hkerOff : ∀ x : ι → ℝ,
      (∀ i, i ≠ r → (Matrix.mulVec H x) i = 0) → ∃ a : ℝ, x = a • q)
    (hdet : (criticalAugmentedMatrix H T q r).det = 0) :
    thirdDirectionalDerivative T q = 0 := by
  have hdot := ClassicalThermodynamics.Math.Matrix.dotProduct_eq_zero_of_det_replaceRow_eq_zero
    H r (thirdDerivativeContraction T q) q hkerOff hdet
  rw [contraction_dot_direction] at hdot
  exact hdot

/-- Full forward-and-converse Reid--Beegle equivalence under the explicit
row-nondegeneracy condition. -/
theorem det_criticalAugmentedMatrix_eq_zero_iff
    [Nonempty ι]
    (H : Matrix ι ι ℝ)
    (T : ThirdDerivativeTensor (ι := ι))
    (q : ι → ℝ) (r : ι)
    (hq : q ≠ 0)
    (_hqr : q r ≠ 0)
    (hHq : Matrix.mulVec H q = 0)
    (hkerOff : ∀ x : ι → ℝ,
      (∀ i, i ≠ r → (Matrix.mulVec H x) i = 0) → ∃ a : ℝ, x = a • q) :
    (criticalAugmentedMatrix H T q r).det = 0 ↔
      thirdDirectionalDerivative T q = 0 := by
  constructor
  · exact thirdDirectionalDerivative_eq_zero_of_det_criticalAugmentedMatrix_eq_zero
      H T q r hkerOff
  · intro hthird
    exact det_criticalAugmentedMatrix_eq_zero H T
      { direction := q
        direction_ne_zero := hq
        hessian_kernel := hHq
        third_directional_zero := hthird } r

end ClassicalThermodynamics.Thermodynamics
