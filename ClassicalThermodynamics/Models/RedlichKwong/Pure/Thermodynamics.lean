import ClassicalThermodynamics.Models.RedlichKwong.Pure.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

namespace ClassicalThermodynamics.Models.RedlichKwong.Pure

/-- Fixed-temperature Helmholtz free-energy density in molar-density coordinates. -/
noncomputable def helmholtzDensity (M : Model) (temperature rho : ℝ) : ℝ :=
  M.gasConstant * temperature * rho *
      (Real.log (rho / (1 - M.excludedVolume * rho)) - 1) -
    attractionScale M temperature * rho / M.excludedVolume *
      Real.log (1 + M.excludedVolume * rho)

/-- Chemical potential compatible with `helmholtzDensity` at fixed temperature. -/
noncomputable def chemicalPotential (M : Model) (temperature rho : ℝ) : ℝ :=
  M.gasConstant * temperature *
      (Real.log (rho / (1 - M.excludedVolume * rho)) +
        M.excludedVolume * rho / (1 - M.excludedVolume * rho)) -
    attractionScale M temperature / M.excludedVolume *
      (Real.log (1 + M.excludedVolume * rho) +
        M.excludedVolume * rho / (1 + M.excludedVolume * rho))

/-- Redlich--Kwong pressure in molar-density coordinates. -/
noncomputable def densityPressure (M : Model) (temperature rho : ℝ) : ℝ :=
  M.gasConstant * temperature * rho / (1 - M.excludedVolume * rho) -
    attractionScale M temperature * rho^2 / (1 + M.excludedVolume * rho)

theorem freeVolume_pos (M : Model) (temperature rho : ℝ)
    (hphysical : PhysicalDensity M temperature rho) :
    0 < 1 - M.excludedVolume * rho := by
  linarith [hphysical.2.2.2]

theorem idealLogArgument_pos (M : Model) (temperature rho : ℝ)
    (hphysical : PhysicalDensity M temperature rho) :
    0 < rho / (1 - M.excludedVolume * rho) :=
  div_pos hphysical.2.2.1 (freeVolume_pos M temperature rho hphysical)

theorem attractionLogArgument_pos (M : Model) (temperature rho : ℝ)
    (hphysical : PhysicalDensity M temperature rho) :
    0 < 1 + M.excludedVolume * rho := by
  have hproduct : 0 < M.excludedVolume * rho :=
    mul_pos hphysical.1.2.1 hphysical.2.2.1
  linarith

/-- The density and molar-volume formulas agree under `rho = 1 / v`. -/
theorem densityPressure_eq_pressure_reciprocal (M : Model) (temperature volume : ℝ)
    (hvolume : volume ≠ 0) (hfree : volume - M.excludedVolume ≠ 0)
    (hattraction : volume + M.excludedVolume ≠ 0) :
    densityPressure M temperature (1 / volume) = pressure M temperature volume := by
  unfold densityPressure pressure attractionScale
  field_simp [hvolume, hfree, hattraction]

/-- Fixed-temperature Legendre identity for the Redlich--Kwong Helmholtz density. -/
theorem densityPressure_eq_rho_mul_chemicalPotential_sub_helmholtzDensity
    (M : Model) (temperature rho : ℝ) (hb : M.excludedVolume ≠ 0)
    (hfree : 1 - M.excludedVolume * rho ≠ 0)
    (hattraction : 1 + M.excludedVolume * rho ≠ 0) :
    densityPressure M temperature rho =
      rho * chemicalPotential M temperature rho - helmholtzDensity M temperature rho := by
  unfold densityPressure chemicalPotential helmholtzDensity
  have hfree' : 1 - rho * M.excludedVolume ≠ 0 := by
    simpa [mul_comm] using hfree
  have hattraction' : 1 + rho * M.excludedVolume ≠ 0 := by
    simpa [mul_comm] using hattraction
  field_simp [hb, hfree, hfree', hattraction, hattraction']
  ring

/-- The fixed-temperature Legendre identity on the physical density domain. -/
theorem densityPressure_eq_rho_mul_chemicalPotential_sub_helmholtzDensity_of_physical
    (M : Model) (temperature rho : ℝ) (hphysical : PhysicalDensity M temperature rho) :
    densityPressure M temperature rho =
      rho * chemicalPotential M temperature rho - helmholtzDensity M temperature rho := by
  apply densityPressure_eq_rho_mul_chemicalPotential_sub_helmholtzDensity
  · exact ne_of_gt hphysical.1.2.1
  · exact ne_of_gt (freeVolume_pos M temperature rho hphysical)
  · exact ne_of_gt (attractionLogArgument_pos M temperature rho hphysical)

end ClassicalThermodynamics.Models.RedlichKwong.Pure
