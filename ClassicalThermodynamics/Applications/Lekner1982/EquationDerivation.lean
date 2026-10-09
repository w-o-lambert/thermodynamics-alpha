import ClassicalThermodynamics.Applications.Lekner1982.PaperEquations
namespace ClassicalThermodynamics.Applications.Lekner1982
open ClassicalThermodynamics.Methods.CoexistenceParametrisation
open ClassicalThermodynamics.Models.VanDerWaals.Pure

theorem derive_equation10_liquid {y : ℝ} (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwLiquidFreeVolume (repositoryParameter y) = paperXLiquidParametric y := by
  simpa [paperXLiquidParametric] using highBranch_eq_lekner hden
theorem derive_equation10_gas {y : ℝ} (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwGasFreeVolume (repositoryParameter y) = paperXGasParametric y := by
  simpa [paperXGasParametric] using lowBranch_eq_lekner hden
theorem derive_equation11 {y : ℝ} (hf : leknerF y ≠ 0) :
    Real.log (paperXLiquidParametric y / paperXGasParametric y) = 2 * y := by
  unfold paperXLiquidParametric paperXGasParametric
  rw [show leknerF y * Real.exp y / (leknerF y * Real.exp (-y)) =
      Real.exp y / Real.exp (-y) by
    field_simp [hf, Real.exp_ne_zero]
    ]
  rw [show Real.exp y / Real.exp (-y) = Real.exp (2 * y) by
    rw [← Real.exp_sub]
    congr 1
    ring, Real.log_exp]
theorem derive_reducedLiquidDensity {y : ℝ} (hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (hliq : Real.exp (-y) + leknerF y ≠ 0) : reducedLiquidDensityLekner y = paperReducedLiquidDensity y := by
  unfold reducedLiquidDensityLekner reducedLiquidDensity reducedDensityFromFreeVolume paperReducedLiquidDensity
  rw [highBranch_eq_lekner hden]
  have hscale : Real.exp y * (Real.exp (-y) + leknerF y) =
      1 + leknerF y * Real.exp y := by
    have hexp : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [mul_add, hexp]
    ring
  have hden' : 1 + leknerF y * Real.exp y ≠ 0 := by
    rw [← hscale]
    exact mul_ne_zero (Real.exp_ne_zero _) hliq
  have hexp : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp [Real.exp_ne_zero, hliq, hden']
  calc
    (leknerF y * Real.exp y) *
        (Real.exp (-y) + leknerF y) =
        leknerF y *
          (Real.exp y * (Real.exp (-y) + leknerF y)) := by ring
    _ = leknerF y * (1 + leknerF y * Real.exp y) := by rw [hscale]
theorem derive_reducedGasDensity {y : ℝ} (hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (hgas : Real.exp y + leknerF y ≠ 0) : reducedGasDensityLekner y = paperReducedGasDensity y := by
  unfold reducedGasDensityLekner reducedGasDensity reducedDensityFromFreeVolume paperReducedGasDensity
  rw [lowBranch_eq_lekner hden]
  have hscale : Real.exp (-y) * (Real.exp y + leknerF y) =
      1 + leknerF y * Real.exp (-y) := by
    have hexp : Real.exp (-y) * Real.exp y = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [mul_add, hexp]
    ring
  have hden' : 1 + leknerF y * Real.exp (-y) ≠ 0 := by
    rw [← hscale]
    exact mul_ne_zero (Real.exp_ne_zero _) hgas
  have hexp : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  field_simp [Real.exp_ne_zero, hgas, hden']
  calc
    (leknerF y * Real.exp (-y)) *
        (Real.exp y + leknerF y) =
        leknerF y *
          (Real.exp (-y) * (Real.exp y + leknerF y)) := by ring
    _ = leknerF y * (1 + leknerF y * Real.exp (-y)) := by rw [hscale]
theorem derive_equation13 {y : ℝ} (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    reducedTemperature y = 27 * leknerF y * (Real.cosh y + leknerF y) / (4 * (leknerG y)^2) := by
  unfold reducedTemperature reducedCoexistenceTemperature
  rw [midpoint_eq_leknerF hden]
  rw [show repositoryParameter y / 2 = y by
    unfold repositoryParameter
    ring]
  rw [← leknerG_eq_genericFreeVolumeProduct hden]
  ring_nf
theorem derive_equation14 {y : ℝ} (hden : Real.sinh y * Real.cosh y - y ≠ 0) :
    reducedPressure y = 27 * (leknerF y)^2 * (1-(leknerF y)^2) / (leknerG y)^2 := by
  unfold reducedPressure reducedCoexistencePressure
  rw [midpoint_eq_leknerF hden]
  rw [← leknerG_eq_genericFreeVolumeProduct hden]
theorem derive_equation15 {y : ℝ} (_hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (hliq : Real.exp (-y) + leknerF y ≠ 0) (hgas : Real.exp y + leknerF y ≠ 0) (hg : leknerG y ≠ 0) :
    (paperReducedLiquidDensity y + paperReducedGasDensity y)/2 = paperMeanReducedDensity y := by
  unfold paperReducedLiquidDensity paperReducedGasDensity paperMeanReducedDensity
  have hgexp : leknerG y =
      1 + leknerF y * (Real.exp y + Real.exp (-y)) + (leknerF y)^2 := by
    unfold leknerG
    rw [Real.cosh_eq]
    ring
  have hgexp' : 1 + leknerF y * (Real.exp y + Real.exp (-y)) +
      (leknerF y)^2 ≠ 0 := by
    rw [← hgexp]
    exact hg
  rw [Real.cosh_eq, hgexp]
  have hexp : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hproduct :
      (Real.exp (-y) + leknerF y) * (Real.exp y + leknerF y) =
        1 + leknerF y * (Real.exp y + Real.exp (-y)) +
          (leknerF y)^2 := by
    calc
      _ = Real.exp (-y) * Real.exp y +
          leknerF y * (Real.exp y + Real.exp (-y)) +
          (leknerF y)^2 := by ring
      _ = _ := by rw [hexp]
  field_simp [hliq, hgas, hgexp', Real.exp_ne_zero]
  rw [← hproduct]
  ring_nf
theorem derive_equation16 {y : ℝ} (_hden : Real.sinh y * Real.cosh y - y ≠ 0)
    (hliq : Real.exp (-y) + leknerF y ≠ 0) (hgas : Real.exp y + leknerF y ≠ 0) (hg : leknerG y ≠ 0) :
    paperReducedLiquidDensity y - paperReducedGasDensity y = paperReducedDensityDifference y := by
  unfold paperReducedLiquidDensity paperReducedGasDensity paperReducedDensityDifference
  rw [Real.sinh_eq]
  have hgexp : leknerG y =
      1 + leknerF y * (Real.exp y + Real.exp (-y)) + (leknerF y)^2 := by
    unfold leknerG
    rw [Real.cosh_eq]
    ring
  have hgexp' : 1 + leknerF y * (Real.exp y + Real.exp (-y)) +
      (leknerF y)^2 ≠ 0 := by
    rw [← hgexp]
    exact hg
  rw [hgexp]
  have hexp : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hproduct :
      (Real.exp (-y) + leknerF y) * (Real.exp y + leknerF y) =
        1 + leknerF y * (Real.exp y + Real.exp (-y)) +
          (leknerF y)^2 := by
    calc
      _ = Real.exp (-y) * Real.exp y +
          leknerF y * (Real.exp y + Real.exp (-y)) +
          (leknerF y)^2 := by ring
      _ = _ := by rw [hexp]
  field_simp [hliq, hgas, hgexp', Real.exp_ne_zero]
  rw [← hproduct]
  ring_nf
end ClassicalThermodynamics.Applications.Lekner1982
