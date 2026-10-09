import ClassicalThermodynamics.Models.Berthelot.Pure.CriticalCoordinates

namespace ClassicalThermodynamics.Models.Berthelot.Pure

/-- Paper Eq. (8), defined directly in reduced density variables. -/
noncomputable def reducedPressureFromDensity (temperature density : ℝ) : ℝ :=
  8 * temperature * density / (3 - density) -
    3 * density^2 / temperature

/-- Equation (8) in denominator-cleared form. -/
lemma reducedEquation_cleared
    (temperature density : ℝ) (hT : temperature ≠ 0)
    (hfree : 3 - density ≠ 0) :
    reducedPressureFromDensity temperature density *
        (temperature * (3 - density)) =
      8 * temperature^2 * density - 3 * density^2 * (3 - density) := by
  unfold reducedPressureFromDensity
  field_simp [hT, hfree]

end ClassicalThermodynamics.Models.Berthelot.Pure
