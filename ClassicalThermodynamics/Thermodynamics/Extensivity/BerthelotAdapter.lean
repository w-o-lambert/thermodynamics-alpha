import ClassicalThermodynamics.Models.Berthelot.Mixture.Thermodynamics
import ClassicalThermodynamics.Models.Berthelot.Mixture.DerivativeProvenance
import ClassicalThermodynamics.Thermodynamics.Extensivity.Construction
import ClassicalThermodynamics.Thermodynamics.Extensivity.Hessian
import ClassicalThermodynamics.Thermodynamics.Extensivity.PressureIdentity

/-!
# Extensive Berthelot mixture adapter

This file is deliberately a direct adapter.  In particular, it does not import
`Extensivity.VanDerWaalsAdapter`: the Berthelot temperature scaling is retained
in the `Berthelot.Mixture` namespace and only the generic extensive
construction, Hessian transfer, and pressure identity are used here.

The derivative certificate is supplied by the model layer.  This keeps this
adapter small while making the dependency explicit, rather than silently
routing a Berthelot result through a van der Waals extensive adapter.
-/

namespace ClassicalThermodynamics.Thermodynamics.Extensivity

open ClassicalThermodynamics.Models.Berthelot.Mixture
open ClassicalThermodynamics.Thermodynamics.Derivatives

noncomputable def berthelotExtensiveFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.Berthelot.Mixture.Model (ι := ι))
    (temperature volume : ℝ) (amount : State (ι := ι)) : ℝ :=
  extensiveFreeEnergy (fun rho => freeEnergy M temperature rho) volume amount

noncomputable def berthelotExtensiveChemicalPotential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.Berthelot.Mixture.Model (ι := ι))
    (temperature : ℝ)
    (volume : ℝ) (amount : State (ι := ι)) (i : ι) : ℝ :=
  extensiveChemicalPotential (chemicalPotential M temperature) volume amount i

theorem berthelot_extensiveFreeEnergy_hasFDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.Berthelot.Mixture.Model (ι := ι))
      (temperature : ℝ)
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : State (ι := ι))
    {D : (State (ι := ι)) →L[ℝ] ℝ}
    (hfree :
      HasFDerivAt (freeEnergy M temperature) D
        (densityState volume amount)) :
    HasFDerivAt
      (fun x : ℝ × State (ι := ι) =>
        berthelotExtensiveFreeEnergy M temperature x.1 x.2)
      (volume •
          (D.comp (ContinuousLinearMap.pi (fun i =>
            (-(amount i / volume ^ 2)) •
                ContinuousLinearMap.fst ℝ ℝ (State (ι := ι)) +
              (volume⁻¹) •
                (ContinuousLinearMap.proj i).comp
                (ContinuousLinearMap.snd ℝ ℝ (State (ι := ι)))))) +
        freeEnergy M temperature (densityState volume amount) •
          ContinuousLinearMap.fst ℝ ℝ (State (ι := ι)))
      (volume, amount) := by
  exact extensiveFreeEnergy_hasFDerivAt_of_densityDerivative
    (fun rho => freeEnergy M temperature rho) hvolume amount hfree

theorem berthelot_extensiveChemicalPotential_hasCoordinateDerivative_hessian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.Berthelot.Mixture.Model (ι := ι))
      (temperature : ℝ)
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : State (ι := ι))
    (hH : HessianDerived (chemicalPotential M temperature)
      (hessian M temperature) (densityState volume amount)) :
    ExtensiveChemicalPotentialHasCoordinateDerivative (chemicalPotential M temperature)
      (hessian M temperature) volume amount :=
  extensiveChemicalPotential_hasCoordinateDerivative_hessian
    (chemicalPotential M temperature) (hessian M temperature)
    hvolume amount hH

theorem berthelot_extensiveChemicalPotential_hasCoordinateDerivative_hessian_of_physical
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.Berthelot.Mixture.Model (ι := ι))
    (temperature : ℝ) {volume : ℝ} (hvolume : volume ≠ 0)
    (amount : State (ι := ι))
    (hphysical :
      ClassicalThermodynamics.Models.Berthelot.Mixture.Physical M
        (densityState volume amount)) :
    ExtensiveChemicalPotentialHasCoordinateDerivative (chemicalPotential M temperature)
      (hessian M temperature) volume amount := by
  apply berthelot_extensiveChemicalPotential_hasCoordinateDerivative_hessian M temperature hvolume amount
  exact ClassicalThermodynamics.Models.Berthelot.Mixture.chemicalPotential_hasCoordinateDerivative_hessian_of_physical
    M temperature (densityState volume amount) hphysical

theorem berthelot_extensive_pressure_identity_of_conjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ClassicalThermodynamics.Models.Berthelot.Mixture.Model (ι := ι))
      (temperature : ℝ)
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : State (ι := ι))
    (P : ℝ) (mu : ι → ℝ)
    {G : (ℝ × State (ι := ι)) →L[ℝ] ℝ}
    (hG :
      HasFDerivAt
        (fun x : ℝ × State (ι := ι) =>
          berthelotExtensiveFreeEnergy M temperature x.1 x.2)
        G (volume, amount))
    (hconj :
      G (volume, amount) = -P * volume + ∑ i, mu i * amount i) :
    P * volume =
      -(volume * freeEnergy M temperature (densityState volume amount)) +
        ∑ i, mu i * amount i := by
  apply extensiveFreeEnergy_pressure_identity_of_conjugate
    (fun rho => freeEnergy M temperature rho) hvolume amount P mu
  · simpa [berthelotExtensiveFreeEnergy] using hG
  · exact hconj

end ClassicalThermodynamics.Thermodynamics.Extensivity
