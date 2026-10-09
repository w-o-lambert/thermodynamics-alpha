import Mathlib.Basic.Real.Basic

namespace ClassicalThermodynamics.Models.Berthelot.Pure

/-- Dimensional Berthelot equation-of-state parameters. -/
structure Model where
  attraction : ℝ
  excludedVolume : ℝ
  gasConstant : ℝ

/-- Paper Eq. (1): `p = RT/(v-b) - a/(T v^2)`. -/
noncomputable def pressure (M : Model) (temperature volume : ℝ) : ℝ :=
  M.gasConstant * temperature / (volume - M.excludedVolume) -
    M.attraction / (temperature * volume^2)

/-- Physical single-phase domain used by the paper. -/
def Physical (M : Model) (temperature volume : ℝ) : Prop :=
  0 < temperature ∧ M.excludedVolume < volume

end ClassicalThermodynamics.Models.Berthelot.Pure
