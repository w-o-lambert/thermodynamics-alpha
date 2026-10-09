import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ClassicalThermodynamics.Models.IdealMixture.Model

open scoped BigOperators

namespace ClassicalThermodynamics.Models.IdealMixture

/-- Ideal-solution entropy of mixing for a composition state. -/
noncomputable def entropyOfMixing {ι : Type*} [Fintype ι]
    (gasConstant : ℝ) (x : State ι) : ℝ :=
  -gasConstant * ∑ i, x.x i * Real.log (x.x i)

/-- The heat of mixing in the ideal-solution model. -/
def heatOfMixing : ℝ := 0

/-- The volume increment of mixing in the ideal-solution model. -/
def volumeOfMixing : ℝ := 0

@[simp] theorem heatOfMixing_eq_zero : heatOfMixing = 0 := rfl

@[simp] theorem volumeOfMixing_eq_zero : volumeOfMixing = 0 := rfl

/-- Ideal-solution entropy of mixing is nonnegative on the composition
simplex for a nonnegative gas constant. -/
theorem entropyOfMixing_nonneg {ι : Type*} [Fintype ι]
    (gasConstant : ℝ) (x : State ι)
    (hR : 0 ≤ gasConstant)
    (hx0 : ∀ i, 0 ≤ x.x i) (hx1 : ∀ i, x.x i ≤ 1) :
    0 ≤ entropyOfMixing gasConstant x := by
  unfold entropyOfMixing
  have hsum : ∑ i, x.x i * Real.log (x.x i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hx0 i)
      (Real.log_nonpos (hx0 i) (hx1 i))
  nlinarith

end ClassicalThermodynamics.Models.IdealMixture
