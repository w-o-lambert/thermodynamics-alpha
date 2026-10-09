import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceObservables

namespace ClassicalThermodynamics.Applications.Lekner1982

open ClassicalThermodynamics.Methods.CoexistenceParametrisation
open ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Lekner's entropy parameter is half the dimensionless entropy difference. The
repository's logarithmic branch separation is therefore `d = 2 y`. -/
noncomputable def repositoryParameter (y : ℝ) : ℝ := 2 * y

/-- Lekner's auxiliary function `f(y)`. -/
noncomputable def leknerF (y : ℝ) : ℝ :=
  (y * Real.cosh y - Real.sinh y) /
    (Real.sinh y * Real.cosh y - y)

/-- Lekner's auxiliary denominator `g(y)`. -/
noncomputable def leknerG (y : ℝ) : ℝ :=
  1 + 2 * leknerF y * Real.cosh y + (leknerF y)^2

/-- Paper-facing aliases of generic coexistence observables. -/
noncomputable def reducedTemperature (y : ℝ) : ℝ :=
  reducedCoexistenceTemperature (repositoryParameter y)

noncomputable def reducedPressure (y : ℝ) : ℝ :=
  reducedCoexistencePressure (repositoryParameter y)

noncomputable def reducedGasDensityLekner (y : ℝ) : ℝ :=
  reducedGasDensity (repositoryParameter y)

noncomputable def reducedLiquidDensityLekner (y : ℝ) : ℝ :=
  reducedLiquidDensity (repositoryParameter y)

noncomputable abbrev reducedDensityFromFreeVolumeLekner :=
  ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedDensityFromFreeVolume

/-- Equation-by-equation core identification: the repository midpoint function
at `d = 2y` is precisely Lekner's `f(y)`. -/
theorem midpoint_eq_leknerF {y : ℝ}
    (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwGeometricMidpoint (repositoryParameter y) = leknerF y := by
  have hy : y ≠ 0 := by
    intro hy
    subst y
    apply hden
    simp
  rw [vdwGeometricMidpoint_eq_formula (by simp [repositoryParameter, hy])]
  unfold vdwGeometricMidpointFormula repositoryParameter leknerF
  have hs : Real.sinh (2 * y) = 2 * Real.sinh y * Real.cosh y := by
    rw [show 2 * y = y + y by ring, Real.sinh_add]
    ring
  rw [hs]
  rw [show 2 * y / 2 = y by ring]
  change (2 * y * Real.cosh y - 2 * Real.sinh y) /
      (2 * Real.sinh y * Real.cosh y - 2 * y) =
    (y * Real.cosh y - Real.sinh y) /
      (Real.sinh y * Real.cosh y - y)
  have hden2 : 2 * Real.sinh y * Real.cosh y - 2 * y ≠ 0 := by
    intro h
    apply hden
    nlinarith
  apply (div_eq_div_iff hden2 hden).2
  ring

/-- The repository high free-volume branch is Lekner's liquid branch coordinate. -/
theorem highBranch_eq_lekner {y : ℝ}
    (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwLiquidFreeVolume (repositoryParameter y) = leknerF y * Real.exp y := by
  unfold vdwLiquidFreeVolume
  rw [midpoint_eq_leknerF hden]
  rw [show repositoryParameter y / 2 = y by simp [repositoryParameter]]

/-- The repository low free-volume branch is Lekner's gas branch coordinate. -/
theorem lowBranch_eq_lekner {y : ℝ}
    (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwGasFreeVolume (repositoryParameter y) = leknerF y * Real.exp (-y) := by
  unfold vdwGasFreeVolume
  rw [midpoint_eq_leknerF hden]
  change leknerF y * Real.exp (-(2 * y) / 2) =
    leknerF y * Real.exp (-y)
  congr 1
  ring

/-- Lekner's reduced liquid density is the repository density transform of the
high free-volume branch. -/
theorem reducedDensity_high_eq_liquid {y : ℝ}
    (_hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (_he : Real.exp (-y) ≠ 0) :
    reducedDensityFromFreeVolumeLekner (vdwLiquidFreeVolume (repositoryParameter y)) =
      reducedLiquidDensityLekner y := by
  unfold reducedDensityFromFreeVolumeLekner reducedLiquidDensityLekner
    reducedDensityFromFreeVolume reducedLiquidDensity
  rfl

/-- Lekner's reduced gas density is the repository density transform of the low
free-volume branch. -/
theorem reducedDensity_low_eq_gas {y : ℝ}
    (_hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (_he : Real.exp y ≠ 0) :
    reducedDensityFromFreeVolumeLekner (vdwGasFreeVolume (repositoryParameter y)) =
      reducedGasDensityLekner y := by
  unfold reducedDensityFromFreeVolumeLekner reducedGasDensityLekner
    reducedDensityFromFreeVolume reducedGasDensity
  rfl

/-- The repository logarithmic branch ratio `d` becomes Lekner's entropy
parameter relation `log(z_l/z_g) = 2y`. -/
theorem entropyParameter_ratio {y : ℝ}
    (hm : vdwGeometricMidpoint (repositoryParameter y) ≠ 0) :
    vdwLiquidFreeVolume (repositoryParameter y) /
      vdwGasFreeVolume (repositoryParameter y) = Real.exp (2 * y) := by
  simpa [repositoryParameter] using
    vdwLiquidFreeVolume_div_vdwGasFreeVolume (d := repositoryParameter y) hm

end ClassicalThermodynamics.Applications.Lekner1982
