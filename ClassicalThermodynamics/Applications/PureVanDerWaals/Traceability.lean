import ClassicalThermodynamics.Models.VanDerWaals.Pure.Stability
import ClassicalThermodynamics.Models.VanDerWaals.Pure.Reconstruction
import ClassicalThermodynamics.Bridges.VanDerWaalsToSecondVirial
/-! The free energy is the model assumption. Other observables and constructions are consequences. -/
namespace ClassicalThermodynamics.Applications.PureVanDerWaals
open ClassicalThermodynamics.Models.VanDerWaals.Pure
open ClassicalThermodynamics.Methods.CoexistenceParametrisation
theorem verified_freeEnergy_modelAssumption (M : Model) (rho : ℝ) :
    freeEnergy M rho = rho * (Real.log (rho / (1 - M.excludedVolume * rho)) - 1) - alpha M * rho^2 := rfl
theorem verified_pressure_formula (M : Model) (rho : ℝ) :
    pressure M rho = rho / (1 - M.excludedVolume * rho) - alpha M * rho^2 := rfl
theorem verified_branch_product (d : ℝ) :
    vdwLiquidFreeVolume d * vdwGasFreeVolume d = (vdwGeometricMidpoint d)^2 := vdwLiquidFreeVolume_mul_vdwGasFreeVolume d

/-- Direct verification of the closed `HvdW` branch formula. -/
theorem verified_closed_HvdW_branches
    {d : ℝ}
    (hm : vdwGeometricMidpoint d ≠ 0)
    (hbranchDiff :
      2 * vdwGeometricMidpoint d * Real.sinh (d / 2) ≠ 0)
    (hpairDen :
      2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
        2 * (vdwGeometricMidpoint d)^2 ≠ 0)
    (hHden : Real.sinh d - d ≠ 0) :
    ParameterFreeCoexistence (vdwLiquidFreeVolume d) (vdwGasFreeVolume d) :=
  vdwBranches_parameterFreeCoexistence hm hbranchDiff hpairDen hHden

theorem verified_secondVirial_decomposition (M : Model) (rho : ℝ)
    (hden : 1 - M.excludedVolume * rho ≠ 0) :
    pressure M rho = ClassicalThermodynamics.Bridges.pressureVirialTruncation M rho +
      ClassicalThermodynamics.Bridges.pressureRemainder M rho :=
  ClassicalThermodynamics.Bridges.pressure_eq_virialTruncation_add_remainder M rho hden
end ClassicalThermodynamics.Applications.PureVanDerWaals
