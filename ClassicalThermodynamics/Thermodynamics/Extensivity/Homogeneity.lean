import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Thermodynamics.Extensivity

def OneHomogeneous {X : Type*} [SMul ℝ X] (F : X → ℝ) : Prop :=
  ∀ (a : ℝ), 0 ≤ a → ∀ x, F (a • x) = a * F x
end ClassicalThermodynamics.Thermodynamics.Extensivity
