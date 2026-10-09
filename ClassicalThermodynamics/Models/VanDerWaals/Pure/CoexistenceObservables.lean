import ClassicalThermodynamics.Models.VanDerWaals.Pure.Entropy
import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

open ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Reduced density relative to the pure van der Waals critical density. -/
noncomputable def reducedDensityFromFreeVolume (z : ℝ) : ℝ :=
  3 * z / (1 + z)

noncomputable def reducedLiquidDensity (d : ℝ) : ℝ :=
  reducedDensityFromFreeVolume (vdwLiquidFreeVolume d)

noncomputable def reducedGasDensity (d : ℝ) : ℝ :=
  reducedDensityFromFreeVolume (vdwGasFreeVolume d)

noncomputable def reducedDensityDifference (d : ℝ) : ℝ :=
  reducedLiquidDensity d - reducedGasDensity d

noncomputable def reducedDensityDiameter (d : ℝ) : ℝ :=
  (reducedLiquidDensity d + reducedGasDensity d) / 2

/-- Product of inverse phase free-volume fractions. -/
noncomputable def coexistenceFreeVolumeProduct (d : ℝ) : ℝ :=
  (1 + vdwLiquidFreeVolume d) * (1 + vdwGasFreeVolume d)

/-- Explicit reduced coexistence temperature. -/
noncomputable def reducedCoexistenceTemperature (d : ℝ) : ℝ :=
  27 * vdwGeometricMidpoint d *
      (vdwGeometricMidpoint d + Real.cosh (d / 2)) /
    (4 * (coexistenceFreeVolumeProduct d)^2)

/-- Explicit reduced coexistence pressure. -/
noncomputable def reducedCoexistencePressure (d : ℝ) : ℝ :=
  27 * (vdwGeometricMidpoint d)^2 *
      (1 - (vdwGeometricMidpoint d)^2) /
    ((coexistenceFreeVolumeProduct d)^2)

/-- Generic free-volume product in midpoint/hyperbolic form. -/
lemma coexistenceFreeVolumeProduct_eq (d : ℝ) :
    coexistenceFreeVolumeProduct d =
      1 + 2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
        (vdwGeometricMidpoint d)^2 := by
  unfold coexistenceFreeVolumeProduct
  have hsum := vdwLiquidFreeVolume_add_vdwGasFreeVolume d
  have hprod := vdwLiquidFreeVolume_mul_vdwGasFreeVolume d
  calc
    (1 + vdwLiquidFreeVolume d) * (1 + vdwGasFreeVolume d) =
        1 + (vdwLiquidFreeVolume d + vdwGasFreeVolume d) +
          vdwLiquidFreeVolume d * vdwGasFreeVolume d := by ring
    _ = 1 + 2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
          vdwGeometricMidpoint d ^ 2 := by rw [hsum, hprod]

/-- The logarithmic branch parameter is the dimensionless entropy difference. -/
theorem entropyDifference_coexistenceBranches
    (M : Model) {d : ℝ}
    (hbpos : 0 < M.excludedVolume)
    (hHigh : 0 < vdwLiquidFreeVolume d) (hLow : 0 < vdwGasFreeVolume d)
    (hm : vdwGeometricMidpoint d ≠ 0) :
    entropyDifferencePerParticle M
      (densityFromFreeVolume M (vdwGasFreeVolume d))
      (densityFromFreeVolume M (vdwLiquidFreeVolume d)) = d := by
  rw [entropyDifference_densityFromFreeVolume M hbpos hHigh hLow]
  rw [vdwLiquidFreeVolume_div_vdwGasFreeVolume hm, Real.log_exp]

end ClassicalThermodynamics.Models.VanDerWaals.Pure
