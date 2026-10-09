import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
open scoped BigOperators
namespace ClassicalThermodynamics.Models.IdealMixture

structure State (ι : Type*) [Fintype ι] where
  x : ι → ℝ
  sum_eq_one : ∑ i, x i = 1

def ActivityCoefficient (_i : ι) : ℝ := 1
end ClassicalThermodynamics.Models.IdealMixture
