import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Hessian
import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture
noncomputable def ofPure
    (M : ClassicalThermodynamics.Models.VanDerWaals.Pure.Model) : Model (ι := Unit) where
  attraction := fun _ _ => 2 * M.attraction
  symmetricAttraction := by ext; rfl
  excludedVolume := fun _ => M.excludedVolume
  gasConstant := M.gasConstant
  temperature := M.temperature
theorem pressure_ofPure
    (M : ClassicalThermodynamics.Models.VanDerWaals.Pure.Model) (rho : ℝ) :
    pressure (ofPure M) (fun _ : Unit => rho) =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure M rho := by
  simp [pressure, totalDensity, freeVolumeFraction, occupiedFraction, alpha,
    ofPure, ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure,
    ClassicalThermodynamics.Models.VanDerWaals.Pure.alpha]
  ring
theorem freeEnergy_ofPure
    (M : ClassicalThermodynamics.Models.VanDerWaals.Pure.Model) (rho : ℝ)
    (hrho : rho ≠ 0) (hfree : 1 - M.excludedVolume * rho ≠ 0) :
    freeEnergy (ofPure M) (fun _ : Unit => rho) =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.freeEnergy M rho := by
  simp [freeEnergy, totalDensity, freeVolumeFraction, occupiedFraction, alpha,
    ofPure, ClassicalThermodynamics.Models.VanDerWaals.Pure.freeEnergy,
    ClassicalThermodynamics.Models.VanDerWaals.Pure.alpha]
  rw [Real.log_div hrho hfree]
  ring
end ClassicalThermodynamics.Models.VanDerWaals.Mixture
