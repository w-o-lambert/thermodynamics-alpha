import ClassicalThermodynamics.Models.VanDerWaals.Pure.ResponseFunctions

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Mechanical response denominator. -/
noncomputable def responseDenominator
    (M : Model) (temperature volume : ℝ) : ℝ :=
  dPdV_atTemperature M temperature volume

/-- Divergence candidate for response functions. -/
def IsResponseSingularity
    (M : Model) (temperature volume : ℝ) : Prop :=
  responseDenominator M temperature volume = 0

@[simp] theorem isothermalCompressibility_eq
    (M : Model) (temperature volume : ℝ) :
    isothermalCompressibility M temperature volume =
      -(1 / volume) / responseDenominator M temperature volume := rfl

@[simp] theorem thermalExpansion_eq
    (M : Model) (temperature volume : ℝ) :
    thermalExpansion M temperature volume =
      -(1 / volume) *
        (dPdT_atVolume M volume / responseDenominator M temperature volume) := rfl

@[simp] theorem heatCapacityDifference_eq
    (M : Model) (temperature volume : ℝ) :
    heatCapacityDifference M temperature volume =
      -temperature * (dPdT_atVolume M volume)^2 /
        responseDenominator M temperature volume := rfl

/-- All three response functions share the same mechanical denominator. -/
theorem common_response_denominator
    (M : Model) (temperature volume : ℝ) :
    responseDenominator M temperature volume =
      dPdV_atTemperature M temperature volume := rfl

end ClassicalThermodynamics.Models.VanDerWaals.Pure
