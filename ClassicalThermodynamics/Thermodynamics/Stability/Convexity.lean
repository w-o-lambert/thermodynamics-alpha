import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
namespace ClassicalThermodynamics.Thermodynamics.Stability

def QuadraticFormPositive {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ) : Prop :=
  ∀ q, q ≠ 0 → 0 < dotProduct q (Matrix.mulVec H q)

def QuadraticFormNonnegative {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ) : Prop :=
  ∀ q, 0 ≤ dotProduct q (Matrix.mulVec H q)

def StrictLocalThermodynamicStability {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) : Prop := QuadraticFormPositive H

def LocalThermodynamicSemistability {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) : Prop := QuadraticFormNonnegative H

/-- Second variation represented explicitly by the Hessian quadratic form. -/
def SecondVariationRepresentedByHessian {ι : Type*} [Fintype ι]
    (secondVariation : (ι → ℝ) → ℝ) (H : Matrix ι ι ℝ) : Prop :=
  ∀ q, secondVariation q = dotProduct q (Matrix.mulVec H q)

/-- Convexity along every admissible line gives a nonnegative second variation. -/
def ConvexSecondVariation {ι : Type*} [Fintype ι]
    (secondVariation : (ι → ℝ) → ℝ) : Prop :=
  ∀ q, 0 ≤ secondVariation q

/-- On a positive-semidefinite Hessian, a zero second variation in a direction
is equivalent to that direction being in the Hessian kernel. -/
theorem zeroSecondVariation_iff_hessianKernel_of_semistable
    {ι : Type*} [Fintype ι] {H : Matrix ι ι ℝ}
    (hH : H.PosSemidef)
    (secondVariation : (ι → ℝ) → ℝ)
    (hRepresentation : SecondVariationRepresentedByHessian secondVariation H)
    (q : ι → ℝ) :
    secondVariation q = 0 ↔ Matrix.mulVec H q = 0 := by
  rw [hRepresentation q]
  simpa using hH.dotProduct_mulVec_zero_iff (x := q)

/-- Convex second variation plus Hessian provenance implies Hessian semidefinite stability. -/
theorem semistability_of_convex_secondVariation
    {ι : Type*} [Fintype ι]
    {secondVariation : (ι → ℝ) → ℝ} {H : Matrix ι ι ℝ}
    (hconvex : ConvexSecondVariation secondVariation)
    (hH : SecondVariationRepresentedByHessian secondVariation H) :
    LocalThermodynamicSemistability H := by
  intro q
  rw [← hH q]
  exact hconvex q

/-- Strict line convexity gives positive-definite Hessian stability. -/
theorem strictStability_of_positive_secondVariation
    {ι : Type*} [Fintype ι]
    {secondVariation : (ι → ℝ) → ℝ} {H : Matrix ι ι ℝ}
    (hpositive : ∀ q, q ≠ 0 → 0 < secondVariation q)
    (hH : SecondVariationRepresentedByHessian secondVariation H) :
    StrictLocalThermodynamicStability H := by
  intro q hq
  rw [← hH q]
  exact hpositive q hq

lemma strictStability_is_positiveQuadraticForm {ι : Type*} [Fintype ι]
    {H : Matrix ι ι ℝ} : StrictLocalThermodynamicStability H ↔ QuadraticFormPositive H := Iff.rfl

end ClassicalThermodynamics.Thermodynamics.Stability
