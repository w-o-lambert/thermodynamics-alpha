import ClassicalThermodynamics.Applications.Lekner1982.Parametrisation
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceCompletion
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceObservables
import ClassicalThermodynamics.Models.VanDerWaals.Pure.ReconstructionCompletion

namespace ClassicalThermodynamics.Applications.Lekner1982

open ClassicalThermodynamics.Methods.CoexistenceParametrisation
open ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Lekner's entropy difference per particle in units of `k_B`. -/
noncomputable def entropyDifference (y : ℝ) : ℝ := repositoryParameter y

@[simp] theorem entropyDifference_eq_repositoryParameter (y : ℝ) :
    entropyDifference y = repositoryParameter y := rfl

/-- The auxiliary identity defining Lekner's `g` is exactly the denominator built
from the repository geometric midpoint and hyperbolic midpoint coordinate. -/
theorem leknerG_eq_repositoryDenominator {y : ℝ}
    (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    leknerG y =
      1 + 2 * vdwGeometricMidpoint (repositoryParameter y) * Real.cosh y +
        (vdwGeometricMidpoint (repositoryParameter y))^2 := by
  rw [midpoint_eq_leknerF hden]
  rfl

/-- The reduced-density difference is exactly the repository high-minus-low
free-volume reconstruction followed by `z ↦ 3z/(1+z)`. -/
theorem densityDifference_comparison {y : ℝ}
    (hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (hep : Real.exp y ≠ 0) (hen : Real.exp (-y) ≠ 0) :
    reducedLiquidDensityLekner y - reducedGasDensityLekner y =
      reducedDensityFromFreeVolumeLekner (vdwLiquidFreeVolume (repositoryParameter y)) -
      reducedDensityFromFreeVolumeLekner (vdwGasFreeVolume (repositoryParameter y)) := by
  rw [reducedDensity_high_eq_liquid hden hen,
      reducedDensity_low_eq_gas hden hep]

/-- The present package's coefficient-free coexistence equation is the algebraic
core solved by Lekner's branch parametrisation after `d = 2y`. -/
theorem leknerBranches_satisfy_repositoryCoexistence
    {y : ℝ}
    (hm : vdwGeometricMidpoint (repositoryParameter y) ≠ 0)
    (hbranchDiff :
      2 * vdwGeometricMidpoint (repositoryParameter y) * Real.sinh y ≠ 0)
    (hpairDen :
      2 * vdwGeometricMidpoint (repositoryParameter y) * Real.cosh y +
        2 * (vdwGeometricMidpoint (repositoryParameter y))^2 ≠ 0)
    (hHden : Real.sinh (2 * y) - 2 * y ≠ 0) :
    ParameterFreeCoexistence
      (vdwLiquidFreeVolume (repositoryParameter y))
      (vdwGasFreeVolume (repositoryParameter y)) := by
  have hbranchDiff' :
      2 * vdwGeometricMidpoint (repositoryParameter y) *
        Real.sinh (repositoryParameter y / 2) ≠ 0 := by
    rw [show repositoryParameter y / 2 = y by
      unfold repositoryParameter
      ring]
    exact hbranchDiff
  have hpairDen' :
      2 * vdwGeometricMidpoint (repositoryParameter y) *
          Real.cosh (repositoryParameter y / 2) +
        2 * (vdwGeometricMidpoint (repositoryParameter y))^2 ≠ 0 := by
    rw [show repositoryParameter y / 2 = y by
      unfold repositoryParameter
      ring]
    exact hpairDen
  simpa [repositoryParameter] using
    vdwBranches_parameterFreeCoexistence
      (d := repositoryParameter y) hm hbranchDiff' hpairDen' hHden

end ClassicalThermodynamics.Applications.Lekner1982

namespace ClassicalThermodynamics.Applications.Lekner1982

open ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Lekner's auxiliary `g` is the generic coexistence free-volume product. -/
theorem leknerG_eq_genericFreeVolumeProduct {y : ℝ}
    (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    leknerG y = coexistenceFreeVolumeProduct (repositoryParameter y) := by
  rw [coexistenceFreeVolumeProduct_eq]
  simpa [repositoryParameter] using leknerG_eq_repositoryDenominator hden

/-- Thin wrapper: Lekner reduced temperature is the generic function at `d=2y`. -/
theorem reducedTemperature_eq_generic (y : ℝ) :
    reducedTemperature y =
      reducedCoexistenceTemperature (repositoryParameter y) := rfl

/-- Thin wrapper: Lekner reduced pressure is the generic function at `d=2y`. -/
theorem reducedPressure_eq_generic (y : ℝ) :
    reducedPressure y =
      reducedCoexistencePressure (repositoryParameter y) := rfl

/-- Thin wrapper for the generic entropy interpretation of the branch parameter. -/
theorem entropyDifference_eq_genericParameter (y : ℝ) :
    entropyDifference y = repositoryParameter y := rfl

end ClassicalThermodynamics.Applications.Lekner1982
