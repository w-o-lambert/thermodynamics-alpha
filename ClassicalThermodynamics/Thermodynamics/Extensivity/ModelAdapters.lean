import ClassicalThermodynamics.Thermodynamics.Extensivity.Construction
import ClassicalThermodynamics.Thermodynamics.Extensivity.Hessian
import ClassicalThermodynamics.Thermodynamics.Extensivity.PressureIdentity
import ClassicalThermodynamics.Models.VanDerWaals.Pure.Thermodynamics
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.HasDerivAtCompletion
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.FrechetProvenance

open scoped BigOperators

namespace ClassicalThermodynamics.Thermodynamics.Extensivity

open ClassicalThermodynamics.Models.VanDerWaals.Mixture

/-- Extensive derivative adapter for a van der Waals mixture. -/
theorem vanDerWaalsMixture_extensiveFreeEnergy_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (M : ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := ι))
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : ι → ℝ)
    {D : (ι → ℝ) →L[ℝ] ℝ}
    (hfree :
      HasFDerivAt (𝕜 := ℝ) (fun rho : ι → ℝ => freeEnergy M rho) D
        (densityState volume amount)) :
    ∃ G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (𝕜 := ℝ)
        (fun x : ℝ × (ι → ℝ) =>
          extensiveFreeEnergy (fun rho => freeEnergy M rho) x.1 x.2)
        G (volume, amount) := by
  let G := (volume •
      (D.comp (ContinuousLinearMap.pi (fun i =>
        (-(amount i / volume ^ 2)) •
          ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) +
        (volume⁻¹) •
          (ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))))) +
      freeEnergy M (densityState volume amount) •
        ContinuousLinearMap.fst ℝ ℝ (ι → ℝ))
  exact ⟨G, extensiveFreeEnergy_hasFDerivAt_of_densityDerivative
    (fun rho => freeEnergy M rho) hvolume amount hfree⟩

theorem vanDerWaalsMixture_extensiveFreeEnergy_hasFDerivAt_of_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := ι))
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : ι → ℝ)
    (hamount : ∀ i, densityState volume amount i ≠ 0)
    (hfree :
      freeVolumeFraction M (densityState volume amount) ≠ 0) :
    ∃ G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (𝕜 := ℝ)
        (fun x : ℝ × (ι → ℝ) =>
          extensiveFreeEnergy (fun rho => freeEnergy M rho) x.1 x.2)
        G (volume, amount) := by
  rcases ClassicalThermodynamics.Models.VanDerWaals.Mixture.freeEnergy_hasFDerivAt
      M (densityState volume amount) hamount hfree with ⟨D, hD⟩
  exact vanDerWaalsMixture_extensiveFreeEnergy_hasFDerivAt
    M hvolume amount hD

theorem vanDerWaalsMixture_extensiveChemicalPotential_hasCoordinateDerivative_hessian_of_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := ι))
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : ι → ℝ)
    (hamount : ∀ i, densityState volume amount i ≠ 0)
    (hfree :
      freeVolumeFraction M (densityState volume amount) ≠ 0) :
    ExtensiveChemicalPotentialHasCoordinateDerivative
      (ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotential M)
      (ClassicalThermodynamics.Models.VanDerWaals.Mixture.hessian M)
      volume amount := by
  exact extensiveChemicalPotential_hasCoordinateDerivative_hessian
    (ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotential M)
    (ClassicalThermodynamics.Models.VanDerWaals.Mixture.hessian M)
    hvolume amount
    (ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotential_hasCoordinateDerivative_hessian
      M (densityState volume amount) hamount hfree)

/-- Canonical van der Waals mixture density identity. -/
theorem vanDerWaalsMixture_pressure_density_adapter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := ι))
    (rho : ι → ℝ)
    (hfree : freeVolumeFraction M rho ≠ 0) :
    pressure M rho =
      (∑ i, rho i * chemicalPotential M rho i) - freeEnergy M rho :=
  pressure_eq_sum_rho_mul_mu_sub_freeEnergy M rho hfree

theorem vanDerWaalsMixture_extensive_pressure_identity_of_conjugate
    {ι : Type*} [Fintype ι]
    (M : ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := ι))
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : ι → ℝ)
    (P : ℝ) (mu : ι → ℝ)
    {G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ}
    (hG :
      HasFDerivAt
        (fun x : ℝ × (ι → ℝ) =>
          extensiveFreeEnergy (fun rho => freeEnergy M rho) x.1 x.2)
        G (volume, amount))
    (hconj : G (volume, amount) = -P * volume + ∑ i, mu i * amount i) :
    P * volume =
      -(volume * freeEnergy M (densityState volume amount)) +
        ∑ i, mu i * amount i :=
  extensiveFreeEnergy_pressure_identity_of_conjugate
    (fun rho => freeEnergy M rho) hvolume amount P mu hG hconj

open ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Canonical pure van der Waals density identity. -/
theorem vanDerWaalsPure_pressure_density_adapter
    (M : ClassicalThermodynamics.Models.VanDerWaals.Pure.Model) (rho : ℝ)
    (hden : 1 - M.excludedVolume * rho ≠ 0) :
    pressure M rho = rho * chemicalPotential M rho - freeEnergy M rho :=
  pressure_eq_rho_mul_mu_sub_freeEnergy M rho hden

end ClassicalThermodynamics.Thermodynamics.Extensivity
