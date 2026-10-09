import ClassicalThermodynamics.Thermodynamics.ResponseFunctions.HeatCapacityDifference
import ClassicalThermodynamics.Thermodynamics.ResponseFunctions

namespace ClassicalThermodynamics.Bridges.ThermodynamicFoundation

/-- The van der Waals consumer formula has the same normalized response form as
the foundation theorem. -/
theorem vanDerWaals_heatCapacityDifference_foundation_form
    (temperature volume dPdT dPdV : ℝ)
    (hV : volume ≠ 0) (hPV : dPdV ≠ 0) :
    ClassicalThermodynamics.Thermodynamics.heatCapacityDifference temperature dPdT dPdV =
      temperature * volume *
        (ClassicalThermodynamics.Thermodynamics.thermalExpansionFromPressureDerivatives
          volume (dPdT / dPdV))^2 /
        ClassicalThermodynamics.Thermodynamics.isothermalCompressibilityFromPressureDerivative
          volume dPdV :=
  ClassicalThermodynamics.Thermodynamics.heatCapacityDifference_eq_expansion_compressibility
    temperature volume dPdT dPdV hV hPV

end ClassicalThermodynamics.Bridges.ThermodynamicFoundation
