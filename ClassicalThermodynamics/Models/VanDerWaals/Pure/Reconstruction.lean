import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
open ClassicalThermodynamics.Methods.CoexistenceParametrisation
noncomputable def coexistenceDensityHigh (M : Model) (d : ℝ) : ℝ :=
  densityFromFreeVolume M (vdwLiquidFreeVolume d)
noncomputable def coexistenceDensityLow (M : Model) (d : ℝ) : ℝ :=
  densityFromFreeVolume M (vdwGasFreeVolume d)
def reducedAttraction_eq_pressureBranchValue (M : Model) (d : ℝ) : Prop :=
  reducedAttraction M = attractionFromPressureEquality (vdwLiquidFreeVolume d) (vdwGasFreeVolume d)
end ClassicalThermodynamics.Models.VanDerWaals.Pure
