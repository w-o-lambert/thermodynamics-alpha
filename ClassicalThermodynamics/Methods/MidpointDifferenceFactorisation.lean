import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF
namespace ClassicalThermodynamics.Methods
noncomputable def scalarMidpoint (a b : ℝ) : ℝ := (a + b) / 2
def scalarDifference (a b : ℝ) : ℝ := a - b
@[simp] theorem scalarMidpoint_add_half_difference (a b : ℝ) :
    scalarMidpoint a b + scalarDifference a b / 2 = a := by
  simp [scalarMidpoint, scalarDifference]; ring
@[simp] theorem scalarMidpoint_sub_half_difference (a b : ℝ) :
    scalarMidpoint a b - scalarDifference a b / 2 = b := by
  simp [scalarMidpoint, scalarDifference]; ring
noncomputable def midpoint {ι : Type*} (a b : ι → ℝ) : ι → ℝ :=
  fun i => scalarMidpoint (a i) (b i)
def difference {ι : Type*} (a b : ι → ℝ) : ι → ℝ :=
  fun i => scalarDifference (a i) (b i)
theorem midpoint_add_half_difference {ι : Type*} (a b : ι → ℝ) :
    (fun i => midpoint a b i + difference a b i / 2) = a := by
  funext i; exact scalarMidpoint_add_half_difference (a i) (b i)
theorem midpoint_sub_half_difference {ι : Type*} (a b : ι → ℝ) :
    (fun i => midpoint a b i - difference a b i / 2) = b := by
  funext i; exact scalarMidpoint_sub_half_difference (a i) (b i)
end ClassicalThermodynamics.Methods

namespace ClassicalThermodynamics.Methods

open scoped BigOperators

/-- A finite weighted sum of a difference is the difference of the weighted sums. -/
theorem weightedSum_difference
    {ι : Type*} [Fintype ι] (w a b : ι → ℝ) :
    (∑ i, w i * difference a b i) =
      (∑ i, w i * a i) - ∑ i, w i * b i := by
  unfold difference scalarDifference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Equality of two finite weighted sums is equivalent to vanishing weighted
difference. -/
theorem weightedSum_eq_iff_difference_eq_zero
    {ι : Type*} [Fintype ι] (w a b : ι → ℝ) :
    (∑ i, w i * a i) = (∑ i, w i * b i) ↔
      ∑ i, w i * difference a b i = 0 := by
  rw [weightedSum_difference]
  constructor <;> intro h <;> linarith

end ClassicalThermodynamics.Methods
