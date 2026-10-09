import ClassicalThermodynamics.Models.Berthelot.Pure.LeknerParametrisation
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceObservables
import ClassicalThermodynamics.Methods.CoexistenceParametrisation.BranchPositivity

namespace ClassicalThermodynamics.Models.Berthelot.Pure

/-- Paper Eq. (25). The square root is the positive physical branch. -/
noncomputable def reducedCoexistenceTemperature (chi : ℝ) : ℝ :=
  3 / (2 * K chi) *
    Real.sqrt (3 * leknerY chi * (leknerY chi + Real.cosh chi))

/-- Paper Eq. (26). -/
noncomputable def reducedCoexistencePressure (chi : ℝ) : ℝ :=
  18 * (leknerY chi)^2 * (1 - (leknerY chi)^2) /
    (K chi * Real.sqrt (3 * leknerY chi *
      (leknerY chi + Real.cosh chi)))

/-- Paper Eq. (27). -/
noncomputable def reducedDensityDifference (chi : ℝ) : ℝ :=
  6 * leknerY chi * Real.sinh chi / K chi

/-- Paper Eq. (28). -/
noncomputable def reducedLatentHeat (chi : ℝ) : ℝ :=
  12 * leknerY chi * Real.sinh chi *
    (3 + 4 * leknerY chi * Real.cosh chi + (leknerY chi)^2) /
    (K chi * Real.sqrt (3 * leknerY chi *
      (leknerY chi + Real.cosh chi)))

/-- Eq. (27) follows algebraically from Eqs. (19)-(21) and (29). -/
theorem liquid_sub_gas_eq_reducedDensityDifference
    (chi : ℝ)
    (hG : leknerY chi + Real.exp chi ≠ 0)
    (hL : leknerY chi + Real.exp (-chi) ≠ 0)
    (hK : K chi ≠ 0) :
    reducedLiquidDensity chi - reducedGasDensity chi =
      reducedDensityDifference chi := by
  let y := leknerY chi
  have hprod :
      (y + Real.exp (-chi)) * (y + Real.exp chi) = K chi := by
    unfold K
    rw [Real.cosh_eq]
    have hexp : Real.exp chi * Real.exp (-chi) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      (y + Real.exp (-chi)) * (y + Real.exp chi) =
          y^2 + y * Real.exp (-chi) + y * Real.exp chi +
            Real.exp (-chi) * Real.exp chi := by ring
      _ = 1 + 2 * y * ((Real.exp chi + Real.exp (-chi)) / 2) + y^2 := by
        rw [mul_comm (Real.exp (-chi)) (Real.exp chi), hexp]
        ring
  calc
    reducedLiquidDensity chi - reducedGasDensity chi =
        3 * y * (Real.exp chi - Real.exp (-chi)) /
          ((y + Real.exp (-chi)) * (y + Real.exp chi)) := by
      unfold reducedLiquidDensity reducedGasDensity
      dsimp [y]
      field_simp [hG, hL]
      ring
    _ = 6 * y * Real.sinh chi / K chi := by
      rw [hprod, Real.sinh_eq]
      field_simp [hK]
      ring
    _ = reducedDensityDifference chi := rfl

/-- Berthelot's paper `K` is the free-volume product of the shared pure-fluid
branches at `d = 2 chi`. -/
theorem K_eq_vdwCoexistenceFreeVolumeProduct
    {chi : ℝ} (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    K chi =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.coexistenceFreeVolumeProduct
        (2 * chi) := by
  have hmid :
      ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
          (2 * chi) = leknerY chi := by
    change
      ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
          (repositoryParameter chi) = leknerY chi
    exact vdwGeometricMidpoint_two_mul_eq_leknerY hden
  rw [ClassicalThermodynamics.Models.VanDerWaals.Pure.coexistenceFreeVolumeProduct_eq]
  unfold K
  rw [← hmid]
  rw [show (2 * chi) / 2 = chi by ring]

/-- The square of the Berthelot reduced temperature is the van der Waals
reduced temperature on the same pure-fluid branch. The models share branch
geometry but retain their distinct temperature maps. -/
theorem reducedCoexistenceTemperature_sq_eq_vdw
    {chi : ℝ} (hchi : 0 < chi)
    (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    reducedCoexistenceTemperature chi ^ 2 =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistenceTemperature
        (2 * chi) := by
  have hmid :
        ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
            (2 * chi) = leknerY chi := by
      change
        ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
            (repositoryParameter chi) = leknerY chi
      exact vdwGeometricMidpoint_two_mul_eq_leknerY hden
  have hK := K_eq_vdwCoexistenceFreeVolumeProduct hden
  have hmidpos :
      0 < ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
        (2 * chi) :=
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint_pos
      (by linarith)
  have hypos : 0 < leknerY chi := by rw [← hmid]; exact hmidpos
  have hcoshpos : 0 < Real.cosh chi := Real.cosh_pos _
  have hradpos : 0 < 3 * leknerY chi *
      (leknerY chi + Real.cosh chi) := by positivity
  have hhighpos :
      0 < ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwLiquidFreeVolume
        (2 * chi) :=
    mul_pos hmidpos (Real.exp_pos _)
  have hlowpos :
      0 < ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGasFreeVolume
        (2 * chi) :=
    mul_pos hmidpos (Real.exp_pos _)
  have hproductpos :
      0 < ClassicalThermodynamics.Models.VanDerWaals.Pure.coexistenceFreeVolumeProduct
        (2 * chi) := by
    unfold ClassicalThermodynamics.Models.VanDerWaals.Pure.coexistenceFreeVolumeProduct
    exact mul_pos (by linarith) (by linarith)
  have hKpos : 0 < K chi := by
    rw [hK]
    exact hproductpos
  have hrad :
      Real.sqrt (3 * leknerY chi * (leknerY chi + Real.cosh chi)) ^ 2 =
        3 * leknerY chi * (leknerY chi + Real.cosh chi) :=
    Real.sq_sqrt (le_of_lt hradpos)
  unfold reducedCoexistenceTemperature
    ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistenceTemperature
  rw [hK, hmid, show (2 * chi) / 2 = chi by ring]
  field_simp [ne_of_gt hKpos]
  nlinarith [hrad]

/-- Berthelot pressure times temperature equals the van der Waals pressure
along the shared branch, reflecting the different attraction-temperature
scaling in the two equations of state. -/
theorem reducedPressure_mul_temperature_eq_vdw
    {chi : ℝ} (hchi : 0 < chi)
    (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    reducedCoexistencePressure chi * reducedCoexistenceTemperature chi =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistencePressure
        (2 * chi) := by
  have hmid :
        ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
            (2 * chi) = leknerY chi := by
      change
        ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
            (repositoryParameter chi) = leknerY chi
      exact vdwGeometricMidpoint_two_mul_eq_leknerY hden
  have hK := K_eq_vdwCoexistenceFreeVolumeProduct hden
  have hmidpos :
      0 < ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint
        (2 * chi) :=
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGeometricMidpoint_pos
      (by linarith)
  have hypos : 0 < leknerY chi := by rw [← hmid]; exact hmidpos
  have hradpos : 0 < 3 * leknerY chi *
      (leknerY chi + Real.cosh chi) := by positivity
  have hhighpos :
      0 < ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwLiquidFreeVolume
        (2 * chi) :=
    mul_pos hmidpos (Real.exp_pos _)
  have hlowpos :
      0 < ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGasFreeVolume
        (2 * chi) :=
    mul_pos hmidpos (Real.exp_pos _)
  have hproductpos :
      0 < ClassicalThermodynamics.Models.VanDerWaals.Pure.coexistenceFreeVolumeProduct
        (2 * chi) := by
    unfold ClassicalThermodynamics.Models.VanDerWaals.Pure.coexistenceFreeVolumeProduct
    exact mul_pos (by linarith) (by linarith)
  have hKpos : 0 < K chi := by
    rw [hK]
    exact hproductpos
  have hrootpos :
      0 < Real.sqrt (3 * leknerY chi * (leknerY chi + Real.cosh chi)) :=
    Real.sqrt_pos.2 hradpos
  unfold reducedCoexistencePressure reducedCoexistenceTemperature
    ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistencePressure
  rw [hK, hmid]
  field_simp [ne_of_gt hKpos, ne_of_gt hrootpos]
  ring

end ClassicalThermodynamics.Models.Berthelot.Pure
