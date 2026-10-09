import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
noncomputable def pressureDerivative (M : Model) (rho : State) : ℝ :=
  1 / (1 - M.excludedVolume * rho)^2 - 2 * alpha M * rho
noncomputable def pressureSecondDerivative (M : Model) (rho : State) : ℝ :=
  2 * M.excludedVolume / (1 - M.excludedVolume * rho)^3 - 2 * alpha M
def IsSpinodal (M : Model) (rho : State) : Prop := pressureDerivative M rho = 0
def IsCritical (M : Model) (rho : State) : Prop :=
  pressureDerivative M rho = 0 ∧ pressureSecondDerivative M rho = 0
noncomputable def criticalDensity (M : Model) : ℝ := 1 / (3 * M.excludedVolume)
noncomputable def criticalTemperature (M : Model) : ℝ :=
  8 * M.attraction / (27 * M.gasConstant * M.excludedVolume)
theorem critical_point_formula (M : Model)
    (ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0) (hR : M.gasConstant ≠ 0) :
    IsCritical { M with temperature := criticalTemperature M } (criticalDensity M) := by
  have h2b : 3 * M.excludedVolume - M.excludedVolume ≠ 0 := by
    intro h
    apply hb
    linarith
  unfold IsCritical pressureDerivative pressureSecondDerivative
    criticalDensity criticalTemperature alpha
  simp only
  constructor <;> field_simp [ha, hb, hR, h2b] <;> ring

end ClassicalThermodynamics.Models.VanDerWaals.Pure
