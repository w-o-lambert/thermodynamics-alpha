import ClassicalThermodynamics.Thermodynamics.ResponseFunctions.HeatCapacityDifference
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace ClassicalThermodynamics.Thermodynamics.Relations

/-- Thermodynamic Joule-Thomson coefficient
`μJT = (T (∂V/∂T)_P - V)/Cp`. -/
noncomputable def jouleThomsonCoefficient (T V dVdT_atP Cp : ℝ) : ℝ :=
  (T * dVdT_atP - V) / Cp

/-- Along a path parameterised by pressure, this is the chain-rule form of
`dH = Cp dT + (V - T (∂V/∂T)_P) dP`. -/
def EnthalpyPathDifferential
    (enthalpy temperature volume volumeSlope heatCapacity temperatureSlope : ℝ → ℝ)
    (p : ℝ) : Prop :=
  HasDerivAt enthalpy
    (heatCapacity p * temperatureSlope p + volume p -
      temperature p * volumeSlope p) p

/-- On an isenthalpic path, the enthalpy differential gives the
Joule-Thomson temperature slope. -/
theorem jouleThomson_of_isenthalpic_path
    (enthalpy temperatureAlongPath temperature volume volumeSlope heatCapacity
      temperatureSlope : ℝ → ℝ) (p : ℝ)
    (hIsenthalpic : HasDerivAt enthalpy 0 p)
    (hDifferential : EnthalpyPathDifferential enthalpy temperature volume
      volumeSlope heatCapacity temperatureSlope p)
    (hTemperature : HasDerivAt temperatureAlongPath (temperatureSlope p) p)
    (hHeatCapacity : heatCapacity p ≠ 0) :
    HasDerivAt temperatureAlongPath
      (jouleThomsonCoefficient (temperature p) (volume p)
        (volumeSlope p) (heatCapacity p)) p := by
  have hPathDerivative :
      0 = heatCapacity p * temperatureSlope p + volume p -
        temperature p * volumeSlope p :=
    hIsenthalpic.unique hDifferential
  have hSlope :
      temperatureSlope p =
        (temperature p * volumeSlope p - volume p) / heatCapacity p := by
    apply (eq_div_iff hHeatCapacity).2
    nlinarith
  rw [hSlope] at hTemperature
  simpa [jouleThomsonCoefficient] using hTemperature

end ClassicalThermodynamics.Thermodynamics.Relations
