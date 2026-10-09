import ClassicalThermodynamics.Models.VanDerWaals.Pure.Model
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
/-- Model assumption: dimensionless Helmholtz free-energy density. -/
noncomputable def freeEnergy (M : Model) (rho : State) : ℝ :=
  rho * (Real.log (rho / (1 - M.excludedVolume * rho)) - 1) - alpha M * rho^2
noncomputable def chemicalPotential (M : Model) (rho : State) : ℝ :=
  Real.log (rho / (1 - M.excludedVolume * rho)) +
    M.excludedVolume * rho / (1 - M.excludedVolume * rho) - 2 * alpha M * rho
noncomputable def pressure (M : Model) (rho : State) : ℝ :=
  rho / (1 - M.excludedVolume * rho) - alpha M * rho^2
theorem pressure_eq_rho_mul_mu_sub_freeEnergy (M : Model) (rho : State)
    (hden : 1 - M.excludedVolume * rho ≠ 0) :
    pressure M rho = rho * chemicalPotential M rho - freeEnergy M rho := by
  unfold pressure chemicalPotential freeEnergy
  have hden' : 1 - rho * M.excludedVolume ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hden, hden']
  ring_nf
def Coexist (M : Model) (rhoA rhoB : State) : Prop :=
  pressure M rhoA = pressure M rhoB ∧ chemicalPotential M rhoA = chemicalPotential M rhoB
end ClassicalThermodynamics.Models.VanDerWaals.Pure
