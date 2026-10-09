import ClassicalThermodynamics.Models.Berthelot.Pure.Model
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

namespace ClassicalThermodynamics.Models.Berthelot.Pure

noncomputable def criticalVolume (M : Model) : ℝ := 3 * M.excludedVolume
noncomputable def criticalTemperature (M : Model) : ℝ :=
  Real.sqrt (8 * M.attraction / (27 * M.gasConstant * M.excludedVolume))
noncomputable def criticalPressure (M : Model) : ℝ :=
  M.gasConstant * criticalTemperature M / (8 * M.excludedVolume)

noncomputable def reducedTemperature (M : Model) (T : ℝ) : ℝ := T / criticalTemperature M
noncomputable def reducedVolume (M : Model) (v : ℝ) : ℝ := v / criticalVolume M
noncomputable def reducedDensity (M : Model) (v : ℝ) : ℝ := criticalVolume M / v
noncomputable def reducedPressure (M : Model) (p : ℝ) : ℝ := p / criticalPressure M

/-- Paper Eq. (2), algebraic critical compressibility factor. -/
theorem criticalCompressibilityFactor_eq_three_eighths
    (M : Model) (hb : M.excludedVolume ≠ 0)
    (hR : M.gasConstant ≠ 0) (hTc : criticalTemperature M ≠ 0) :
    criticalPressure M * criticalVolume M /
      (M.gasConstant * criticalTemperature M) = 3 / 8 := by
  unfold criticalPressure criticalVolume
  field_simp [hb, hR, hTc]

end ClassicalThermodynamics.Models.Berthelot.Pure
