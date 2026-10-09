import ClassicalThermodynamics.Models.VanDerWaals.Pure.Stability
import ClassicalThermodynamics.Models.VanDerWaals.Pure.ResponseFunctions

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

noncomputable def criticalPressure (M : Model) : ℝ :=
  M.attraction / (27 * M.excludedVolume^2)

noncomputable def criticalVolume (M : Model) : ℝ := 3 * M.excludedVolume

noncomputable def criticalCompressibilityFactor (M : Model) : ℝ :=
  criticalPressure M * criticalVolume M /
    (M.gasConstant * criticalTemperature M)

/-- The dimensional equation of state evaluated at the standard critical
coordinates gives the standard critical pressure. -/
theorem pressureTV_critical_coordinates
    (M : Model) (_ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0)
    (hR : M.gasConstant ≠ 0) :
    pressureTV M (criticalTemperature M) (criticalVolume M) =
      criticalPressure M := by
  unfold pressureTV criticalTemperature criticalVolume criticalPressure
  have h2b : 3 * M.excludedVolume - M.excludedVolume =
      2 * M.excludedVolume := by ring
  rw [h2b]
  field_simp [hb, hR]
  norm_num

/-- Universal van der Waals critical compressibility factor. -/
theorem criticalCompressibilityFactor_eq
    (M : Model) (ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0)
    (hR : M.gasConstant ≠ 0) :
    criticalCompressibilityFactor M = 3 / 8 := by
  unfold criticalCompressibilityFactor criticalPressure criticalVolume criticalTemperature
  field_simp [ha, hb, hR]

end ClassicalThermodynamics.Models.VanDerWaals.Pure
