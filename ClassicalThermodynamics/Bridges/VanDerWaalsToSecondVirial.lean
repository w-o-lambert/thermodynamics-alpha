import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
namespace ClassicalThermodynamics.Bridges
open ClassicalThermodynamics.Models.VanDerWaals.Pure
noncomputable def vanDerWaalsSecondVirial (M : Model) : ℝ := M.excludedVolume - alpha M
noncomputable def pressureVirialTruncation (M : Model) (rho : ℝ) : ℝ :=
  rho + vanDerWaalsSecondVirial M * rho^2
noncomputable def pressureRemainder (M : Model) (rho : ℝ) : ℝ :=
  M.excludedVolume^2 * rho^3 / (1 - M.excludedVolume * rho)
theorem pressure_eq_virialTruncation_add_remainder (M : Model) (rho : ℝ)
    (hden : 1 - M.excludedVolume * rho ≠ 0) :
    pressure M rho = pressureVirialTruncation M rho + pressureRemainder M rho := by
  unfold pressure pressureVirialTruncation pressureRemainder vanDerWaalsSecondVirial
  have hden' : 1 - rho * M.excludedVolume ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hden, hden']
  ring_nf
end ClassicalThermodynamics.Bridges
