import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
structure Model where
  attraction : ℝ
  excludedVolume : ℝ
  gasConstant : ℝ
  temperature : ℝ
abbrev State := ℝ
def Physical (M : Model) (rho : State) : Prop :=
  0 < rho ∧ M.excludedVolume * rho < 1
noncomputable def alpha (M : Model) : ℝ :=
  M.attraction / (M.gasConstant * M.temperature)
noncomputable def reducedAttraction (M : Model) : ℝ :=
  alpha M / M.excludedVolume
end ClassicalThermodynamics.Models.VanDerWaals.Pure
