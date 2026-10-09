import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics
import ClassicalThermodynamics.Thermodynamics.ResponseFunctions

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mole fractions used for fixed-composition response functions. -/
def NormalizedComposition (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- Molar covolume at fixed composition. -/
noncomputable def mixtureCovolume (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * M.excludedVolume i

/-- Molar attraction at fixed composition. -/
noncomputable def mixtureAttraction (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M.attraction i j * x j / 2

/-- Dimensional one-fluid pressure along a fixed-composition ray. -/
noncomputable def pressureTVAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ)
    (temperature molarVolume : ℝ) : ℝ :=
  M.gasConstant * temperature / (molarVolume - mixtureCovolume M x) -
    mixtureAttraction M x / molarVolume^2

noncomputable def dPdT_atVolumeComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (molarVolume : ℝ) : ℝ :=
  M.gasConstant / (molarVolume - mixtureCovolume M x)

noncomputable def dPdV_atTemperatureComposition
    (M : Model (ι := ι)) (x : ι → ℝ)
    (temperature molarVolume : ℝ) : ℝ :=
  -M.gasConstant * temperature /
      (molarVolume - mixtureCovolume M x)^2 +
    2 * mixtureAttraction M x / molarVolume^3

noncomputable def thermalExpansionAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ)
    (temperature molarVolume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.thermalExpansionFromPressureDerivatives molarVolume
    (dPdT_atVolumeComposition M x molarVolume /
      dPdV_atTemperatureComposition M x temperature molarVolume)

noncomputable def isothermalCompressibilityAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ)
    (temperature molarVolume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.isothermalCompressibilityFromPressureDerivative molarVolume
    (dPdV_atTemperatureComposition M x temperature molarVolume)

noncomputable def heatCapacityDifferenceAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ)
    (temperature molarVolume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.heatCapacityDifference temperature
    (dPdT_atVolumeComposition M x molarVolume)
    (dPdV_atTemperatureComposition M x temperature molarVolume)

noncomputable def heatCapacityAtConstantPressureAtComposition
    (M : Model (ι := ι)) (C : ClassicalThermodynamics.Thermodynamics.CaloricModel)
    (x : ι → ℝ) (temperature molarVolume : ℝ) : ℝ :=
  ClassicalThermodynamics.Thermodynamics.heatCapacityAtConstantVolume C temperature +
    heatCapacityDifferenceAtComposition M x temperature molarVolume

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
