import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Models.IdealGas
structure Model where gasConstant : ℝ
def EquationOfState (M : Model) (n T V P : ℝ) : Prop := P * V = n * M.gasConstant * T
end ClassicalThermodynamics.Models.IdealGas
