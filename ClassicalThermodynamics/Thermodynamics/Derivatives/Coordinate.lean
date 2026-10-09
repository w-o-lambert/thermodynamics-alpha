import Mathlib.Analysis.Calculus.Deriv.Basic
import ClassicalThermodynamics.Math.Functions.CoordinatePerturbation
namespace ClassicalThermodynamics.Thermodynamics.Derivatives

def coordinatePerturb {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (i : ι) (t : ℝ) : ι → ℝ :=
  ClassicalThermodynamics.Math.Functions.coordinatePerturb x i t

@[simp] theorem coordinatePerturb_same {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (i : ι) (t : ℝ) :
    coordinatePerturb x i t i = x i + t := by
  exact ClassicalThermodynamics.Math.Functions.coordinatePerturb_apply_same x i t

@[simp] theorem coordinatePerturb_other {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) {i j : ι} (h : j ≠ i) (t : ℝ) :
    coordinatePerturb x i t j = x j := by
  exact ClassicalThermodynamics.Math.Functions.coordinatePerturb_apply_of_ne x h t

def CoordinateDerivativeDerived {ι : Type*} [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (D : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : Prop :=
  ∀ i, HasDerivAt (fun t => F (coordinatePerturb x i t)) (D x i) 0

end ClassicalThermodynamics.Thermodynamics.Derivatives
