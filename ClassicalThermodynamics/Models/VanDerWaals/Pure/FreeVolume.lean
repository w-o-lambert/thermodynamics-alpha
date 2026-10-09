import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
noncomputable def freeVolumeDensity (M : Model) (rho : State) : ℝ :=
  M.excludedVolume * rho / (1 - M.excludedVolume * rho)
noncomputable def densityFromFreeVolume (M : Model) (y : ℝ) : State :=
  y / (M.excludedVolume * (1 + y))
noncomputable def transformedChemicalPotential (q y : ℝ) : ℝ :=
  Real.log y + y - 2 * q * y / (1 + y)
noncomputable def transformedPressure (q y : ℝ) : ℝ := y - q * y^2 / (1 + y)^2
theorem densityFromFreeVolume_freeVolumeDensity (M : Model) (rho : State)
    (hb : M.excludedVolume ≠ 0) (hden : 1 - M.excludedVolume * rho ≠ 0) :
    densityFromFreeVolume M (freeVolumeDensity M rho) = rho := by
  unfold densityFromFreeVolume freeVolumeDensity
  field_simp [hb, hden]
  ring

/-- Free-volume density ratio after reconstructing density from `y`. -/
theorem densityFromFreeVolume_div_freeFraction
    (M : Model) (y : ℝ) (hb : M.excludedVolume ≠ 0) (hy : 1 + y ≠ 0) :
    densityFromFreeVolume M y /
      (1 - M.excludedVolume * densityFromFreeVolume M y) =
    y / M.excludedVolume := by
  unfold densityFromFreeVolume
  field_simp [hb, hy]
  ring

theorem pressure_densityFromFreeVolume (M : Model) (y : ℝ)
    (hb : M.excludedVolume ≠ 0) (hy : 1 + y ≠ 0) :
    M.excludedVolume * pressure M (densityFromFreeVolume M y) =
      transformedPressure (reducedAttraction M) y := by
  have hfree :
      1 - M.excludedVolume * densityFromFreeVolume M y = 1 / (1 + y) := by
    unfold densityFromFreeVolume
    field_simp [hb, hy]
    ring
  have hideal :
      M.excludedVolume *
          (densityFromFreeVolume M y /
            (1 - M.excludedVolume * densityFromFreeVolume M y)) = y := by
    rw [densityFromFreeVolume_div_freeFraction M y hb hy]
    field_simp [hb]
  have hsq :
      (densityFromFreeVolume M y) ^ 2 =
        y ^ 2 / (M.excludedVolume ^ 2 * (1 + y) ^ 2) := by
    unfold densityFromFreeVolume
    rw [div_pow]
    congr 1
    ring
  have hattr :
      M.excludedVolume * (alpha M * (densityFromFreeVolume M y) ^ 2) =
        reducedAttraction M * y ^ 2 / (1 + y) ^ 2 := by
    rw [hsq]
    unfold reducedAttraction
    field_simp [hb, hy]
  unfold pressure transformedPressure
  rw [mul_sub, hideal, hattr]

end ClassicalThermodynamics.Models.VanDerWaals.Pure
