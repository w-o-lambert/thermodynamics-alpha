import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Thermodynamics

/-- Volumetric thermal expansion from pressure derivatives. -/
noncomputable def thermalExpansionFromPressureDerivatives
    (volume dPdT_dV : ℝ) : ℝ :=
  -(1 / volume) * dPdT_dV

/-- Isothermal compressibility from the isothermal volume derivative of pressure. -/
noncomputable def isothermalCompressibilityFromPressureDerivative
    (volume dPdV : ℝ) : ℝ :=
  -(1 / volume) / dPdV

/-- Generic response identity `C_P - C_V`. -/
noncomputable def heatCapacityDifference
    (temperature dPdT dPdV : ℝ) : ℝ :=
  -temperature * dPdT^2 / dPdV

/-- Equivalent response identity `T V alpha_P^2 / kappa_T`. -/
theorem heatCapacityDifference_eq_expansion_compressibility
    (temperature volume dPdT dPdV : ℝ)
    (hV : volume ≠ 0) (hPV : dPdV ≠ 0) :
    heatCapacityDifference temperature dPdT dPdV =
      temperature * volume *
        (thermalExpansionFromPressureDerivatives volume (dPdT / dPdV))^2 /
        isothermalCompressibilityFromPressureDerivative volume dPdV := by
  unfold heatCapacityDifference thermalExpansionFromPressureDerivatives
    isothermalCompressibilityFromPressureDerivative
  field_simp [hV, hPV]

/-- Additional caloric input. An equation of state does not determine absolute
heat capacities; `cv` is supplied independently. -/
structure CaloricModel where
  cv : ℝ → ℝ

noncomputable def heatCapacityAtConstantVolume
    (C : CaloricModel) (temperature : ℝ) : ℝ := C.cv temperature

noncomputable def heatCapacityAtConstantPressure
    (C : CaloricModel) (temperature dPdT dPdV : ℝ) : ℝ :=
  heatCapacityAtConstantVolume C temperature +
    heatCapacityDifference temperature dPdT dPdV

@[simp] theorem cp_sub_cv
    (C : CaloricModel) (temperature dPdT dPdV : ℝ) :
    heatCapacityAtConstantPressure C temperature dPdT dPdV -
      heatCapacityAtConstantVolume C temperature =
        heatCapacityDifference temperature dPdT dPdV := by
  unfold heatCapacityAtConstantPressure
  ring

end ClassicalThermodynamics.Thermodynamics
