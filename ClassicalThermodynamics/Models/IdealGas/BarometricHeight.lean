import ClassicalThermodynamics.Models.IdealGas.Model
import Mathlib.Analysis.SpecialFunctions.Exp
namespace ClassicalThermodynamics.Models.IdealGas
/-- Isothermal barometric pressure law. -/
noncomputable def barometricPressure (P0 molarMass gravity R T height : ℝ) : ℝ :=
  P0 * Real.exp (-(molarMass * gravity * height) / (R * T))
@[simp] theorem barometricPressure_zero (P0 molarMass gravity R T : ℝ) :
    barometricPressure P0 molarMass gravity R T 0 = P0 := by
  unfold barometricPressure
  simp
end ClassicalThermodynamics.Models.IdealGas
