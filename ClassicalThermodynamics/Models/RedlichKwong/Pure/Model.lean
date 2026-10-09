import Mathlib.Analysis.Real.Sqrt

namespace ClassicalThermodynamics.Models.RedlichKwong.Pure

/-- Dimensional parameters of the pure Redlich--Kwong equation of state. -/
structure Model where
  attraction : ℝ
  excludedVolume : ℝ
  gasConstant : ℝ

/-- Positivity assumptions for a physically admissible pure Redlich--Kwong model. -/
def Parameters (M : Model) : Prop :=
  0 < M.attraction ∧ 0 < M.excludedVolume ∧ 0 < M.gasConstant

/-- The physical molar-volume domain at a fixed positive temperature. -/
def Physical (M : Model) (temperature volume : ℝ) : Prop :=
  Parameters M ∧ 0 < temperature ∧ M.excludedVolume < volume

/-- The physical molar-density domain corresponding to `Physical`. -/
def PhysicalDensity (M : Model) (temperature rho : ℝ) : Prop :=
  Parameters M ∧ 0 < temperature ∧ 0 < rho ∧ M.excludedVolume * rho < 1

/-- The temperature-scaled Redlich--Kwong attraction coefficient, `a / √T`. -/
noncomputable def attractionScale (M : Model) (temperature : ℝ) : ℝ :=
  M.attraction / Real.sqrt temperature

/-- Redlich--Kwong pressure in molar-volume coordinates:
`p(T,v) = R T / (v - b) - a / (√T v (v + b))`. -/
noncomputable def pressure (M : Model) (temperature volume : ℝ) : ℝ :=
  M.gasConstant * temperature / (volume - M.excludedVolume) -
    M.attraction / (Real.sqrt temperature * volume * (volume + M.excludedVolume))

end ClassicalThermodynamics.Models.RedlichKwong.Pure
