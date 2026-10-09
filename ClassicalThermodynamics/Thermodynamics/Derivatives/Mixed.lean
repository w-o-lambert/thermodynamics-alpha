import ClassicalThermodynamics.Thermodynamics.Derivatives.Coordinate
import ClassicalThermodynamics.Thermodynamics.Derivatives.Control
namespace ClassicalThermodynamics.Thermodynamics.Derivatives

def MixedControlCoordinateDerivativeDerived {ι : Type*} [DecidableEq ι]
    (stateDerivative : ℝ → (ι → ℝ) → ι → ℝ)
    (mixed : ℝ → (ι → ℝ) → ι → ℝ)
    (control : ℝ) (x : ι → ℝ) : Prop :=
  ∀ i, HasDerivAt (fun t => stateDerivative t x i) (mixed control x i) control

def MixedCoordinateControlDerivativeDerived {ι : Type*} [DecidableEq ι]
    (controlDerivative : ℝ → (ι → ℝ) → ℝ)
    (mixed : ℝ → (ι → ℝ) → ι → ℝ)
    (control : ℝ) (x : ι → ℝ) : Prop :=
  ∀ i, HasDerivAt
    (fun t => controlDerivative control (coordinatePerturb x i t))
    (mixed control x i) 0

end ClassicalThermodynamics.Thermodynamics.Derivatives
