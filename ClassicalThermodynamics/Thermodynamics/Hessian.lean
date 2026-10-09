import ClassicalThermodynamics.Thermodynamics.FreeEnergy
import Mathlib.Data.Matrix.Basic
namespace ClassicalThermodynamics.Thermodynamics
class HasHessian (iota State Model : Type*) where
  hessian : Model -> State -> Matrix iota iota Real
end ClassicalThermodynamics.Thermodynamics
