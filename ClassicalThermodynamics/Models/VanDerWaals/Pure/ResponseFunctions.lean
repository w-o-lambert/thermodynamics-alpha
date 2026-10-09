import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
import ClassicalThermodynamics.Thermodynamics.ResponseFunctions

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Dimensional pressure as a function of temperature and molar volume. -/
noncomputable def pressureTV (M : Model) (temperature volume : ℝ) : ℝ :=
  M.gasConstant * temperature / (volume - M.excludedVolume) -
    M.attraction / volume^2

noncomputable def dPdT_atVolume (M : Model) (volume : ℝ) : ℝ :=
  M.gasConstant / (volume - M.excludedVolume)

noncomputable def dPdV_atTemperature
    (M : Model) (temperature volume : ℝ) : ℝ :=
  -M.gasConstant * temperature / (volume - M.excludedVolume)^2 +
    2 * M.attraction / volume^3

noncomputable def thermalExpansion
    (M : Model) (temperature volume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.thermalExpansionFromPressureDerivatives volume
    (dPdT_atVolume M volume / dPdV_atTemperature M temperature volume)

noncomputable def isothermalCompressibility
    (M : Model) (temperature volume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.isothermalCompressibilityFromPressureDerivative volume
    (dPdV_atTemperature M temperature volume)

noncomputable def heatCapacityDifference
    (M : Model) (temperature volume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.heatCapacityDifference temperature
    (dPdT_atVolume M volume) (dPdV_atTemperature M temperature volume)

noncomputable def heatCapacityAtConstantVolume
    (C : ClassicalThermodynamics.Thermodynamics.CaloricModel) (temperature : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.heatCapacityAtConstantVolume C temperature

noncomputable def heatCapacityAtConstantPressure
    (M : Model) (C : ClassicalThermodynamics.Thermodynamics.CaloricModel)
    (temperature volume : ℝ) : ℝ :=
  heatCapacityAtConstantVolume C temperature +
    heatCapacityDifference M temperature volume

@[simp] theorem cp_sub_cv
    (M : Model) (C : ClassicalThermodynamics.Thermodynamics.CaloricModel)
    (temperature volume : ℝ) :
    heatCapacityAtConstantPressure M C temperature volume -
      heatCapacityAtConstantVolume C temperature =
        heatCapacityDifference M temperature volume := by
  unfold heatCapacityAtConstantPressure
  ring

end ClassicalThermodynamics.Models.VanDerWaals.Pure
